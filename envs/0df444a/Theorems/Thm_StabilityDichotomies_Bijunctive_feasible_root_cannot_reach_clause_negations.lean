-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_feasible_root_cannot_reach_clause_negations
-- name    : StabilityDichotomies.Bijunctive.feasible_root_cannot_reach_clause_negations
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:09:14.380991+00:00
-- url     : https://prove2.me/theorems/eac63a03-1d0d-40c4-9d3d-7c4e025a03af
-- title:
--   A feasible root cannot imply both negations of a retained clause
-- statement:
--   Let I₁ be a constraint subinstance of I₂, let q be a two-CNF clause of a constraint retained in I₁, and let a root literal be feasible in I₂. In the implication graph of I₁, that root cannot reach the negations of both substituted literals of q. The witnessing satisfying assignment would make both clause literals false. This is the source proof’s disjointness of feasible root sets for a retained clause.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.9, p. 20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.feasible_root_cannot_reach_clause_negations {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (I₁ I₂ : Instance Γ V)
    (hsub : ∀ c ∈ I₁.constraints, c ∈ I₂.constraints)
    (c : Constraint Γ V) (hc : c ∈ I₁.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (root : Literal V) (hroot : feasibleLiteral I₂ root) :
    ¬ (∃ n m : ℕ, WalkLength (implicationArc rep I₁) n root (literalNeg (substituteClause c q).1) ∧
      WalkLength (implicationArc rep I₁) m root (literalNeg (substituteClause c q).2)) := by sorry
