import InferenceInLean.A_Syntax
import InferenceInLean.B_Semantics
import InferenceInLean.C_Models

set_option autoImplicit false
--set_option diagnostics true

open Syntax
open Semantics
open Models

/- ### Unification -/

namespace Unification

@[simp]
abbrev Equality (sig : Signature) (X : Variables) :=
  Atom sig X × Atom sig X

@[simp]
abbrev EqualityProblem (sig : Signature) (X : Variables) :=
  List (Equality sig X)

instance {sig : Signature} {X : Variables} : Membership (Equality sig X) (EqualityProblem sig X) :=
  List.instMembership

@[simp]
def EqualityProblem.freeVars {sig : Signature} {X : Variables} :
    EqualityProblem sig X -> Set X
  | [] => ∅
  | (lhs, rhs) :: eqs => Atom.freeVars lhs ∪ Atom.freeVars rhs ∪ freeVars eqs

@[simp]
def Unifier {sig : Signature} {X : Variables} [DecidableEq X]
    (E : EqualityProblem sig X) (σ : Substitution sig X) : Prop :=
  ∀ eq ∈ E, have ⟨lhs, rhs⟩ := eq; lhs.substitute σ = rhs.substitute σ

def example_unification_problem : EqualityProblem (Signature.mk String String) String :=
  [(.pred "P" [.func "f" [Term.var "x"]], .pred "P" [Term.var "y"])]

def example_unifier : Substitution (Signature.mk String String) String :=
  fun x => if x == "y" then Term.func "f" [Term.var "x"] else Term.var x

theorem example_unification : Unifier example_unification_problem example_unifier := by
  simp [example_unification_problem, example_unifier]

@[simp]
def MostGeneralUnifier {sig : Signature} {X : Variables} [DecidableEq X]
    (E : EqualityProblem sig X) (σ : Substitution sig X) : Prop :=
  Unifier E σ ∧ (∀ τ : Substitution sig X, Unifier E τ → σ ≤ τ)

lemma mgu_imp_unifier {sig : Signature} {X : Variables} [DecidableEq X] (E : EqualityProblem sig X)
    (σ : Substitution sig X) : MostGeneralUnifier E σ → Unifier E σ := fun ⟨h, _⟩ => h

@[simp]
def Unifiable {sig : Signature} {X : Variables} [DecidableEq X]
  (E : EqualityProblem sig X) : Prop := ∃ σ : Substitution sig X, Unifier E σ



  def unification_alg {sig : Signature} {X : Variables} [DecidableEq X] [DecidableEq (Atom sig X)] [DecidableEq (Term sig X)]
  (E : EqualityProblem sig X) : Option (Substitution sig X) := sorry


     --match E with
    --| [] => some (fun x => Term.var x)
    --| (lhs, rhs) :: rest =>
     --   if ss = ts then unification_alg rest
       -- else
         -- match lhs, rhs with
           -- | .pred p ss, .pred q ts =>
             -- if p = q ∧ ss.length = ts.length then unification_alg (ss.zip ts)
              --else none
          --  | .var x, t =>
          --      sorry -- Occurs-Check und x durch t ersetzen
         -- | .func f ss, .var x =>
          --      sorry -- Variable nach links bringen
          --  | .func f ss, .func g ts =>
          --      sorry -- Funktionssymbole vergleichen und ggf. zerlegen
          --| .func f, .var x => .var x, .func f


theorem unifiable_iff_mgu_idempot {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (E : EqualityProblem sig X) : Unifiable E ↔ ∃ σ : Substitution sig X,
      MostGeneralUnifier E σ ∧ Idempotent σ ∧ σ.domain ∪ σ.codomain ⊆ E.freeVars := by
  apply Iff.intro
  · sorry
    /- This direction would need the standard unification algorithm.
    I have played around with implementing it but it brings quite some chanllenge with it and feels
    like it's outside the scope of this project.
      -/
  · intro h
    obtain ⟨σ, ⟨⟨⟩⟩⟩ := h
    use σ
alias main_unification_theorem := unifiable_iff_mgu_idempot
