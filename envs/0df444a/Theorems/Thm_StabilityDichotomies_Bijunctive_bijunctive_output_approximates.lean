-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_approximates
-- name    : StabilityDichotomies.Bijunctive.bijunctive_output_approximates
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:07:41.972243+00:00
-- url     : https://prove2.me/theorems/02faf9ae-8fb9-452b-80db-7c5eeaa85cdc
-- title:
--   Approximation guarantee for the exact bijunctive output law
-- statement:
--   Fix correct bounded two-CNF representations, 0 < ε ≤ 1, and a solver with the exact Definition 4.8 product-measure output law. Then the solver violates at most an ε fraction of constraints in expectation on each satisfiable instance. This is the approximation half of Theorem 4.9; the probability argument and source shifted-exponential gap bound remain open.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.9, pp. 19–21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_output_approximates (Γ : Language) (rep : TwoCNFRepresentation Γ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (A : Solver Γ)
    (hLaw : BijunctiveOutputLaw Γ rep ε A) : Approximates A ε := by
  sorry
