-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_score_decreases_when_feasible_roots_shrink
-- name    : StabilityDichotomies.Bijunctive.score_decreases_when_feasible_roots_shrink
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:21:24.614494+00:00
-- url     : https://prove2.me/theorems/ac2ca883-c45b-41a7-bc63-bcbcf051a2fc
-- title:
--   Adding feasibility constraints cannot increase a literal score
-- statement:
--   With graph and shifts fixed, adding constraints to the feasibility-testing instance can only remove feasible roots and therefore cannot increase any literal score.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.score_decreases_when_feasible_roots_shrink {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F F' : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ c ∈ F.constraints, c ∈ F'.constraints) (target : Literal V) :
    literalScore rep G F' δ target ≤ literalScore rep G F δ target := by
  sorry
