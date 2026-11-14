-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_feasible_root_cannot_reach_opposites
-- name    : StabilityDichotomies.Bijunctive.feasible_root_cannot_reach_opposites
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:46:00.705366+00:00
-- url     : https://prove2.me/theorems/b983d061-d3bd-465b-8f6e-ba3f7e3a37a7
-- title:
--   A feasible root cannot imply opposite literals in a nested subinstance
-- statement:
--   Fix a correct two-CNF representation, and let every constraint of I₁ occur in I₂. If a literal is feasible in I₂, then the implication graph of I₁ contains no directed paths from that root to both a literal and its negation. The proof follows a satisfying assignment along each implication arc and path. This is the deterministic feasibility observation used at the beginning of the proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.9, pp. 19–20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.feasible_root_cannot_reach_opposites {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (I₁ I₂ : Instance Γ V)
    (hsub : ∀ c ∈ I₁.constraints, c ∈ I₂.constraints)
    (root target : Literal V) (hroot : feasibleLiteral I₂ root) :
    ¬ (∃ n m : ℕ, WalkLength (implicationArc rep I₁) n root target ∧
      WalkLength (implicationArc rep I₁) m root (literalNeg target)) := by sorry
