-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_is_probability
-- name    : StabilityDichotomies.Bijunctive.bijunctive_seed_is_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:46:45.466285+00:00
-- url     : https://prove2.me/theorems/7bc8aaec-7709-4a0d-b701-014c8d5bbe87
-- title:
--   The bijunctive algorithm seed measure is a probability measure
-- statement:
--   For ε > 0 and a fixed two-CNF representation with positive clause bound, the seed measure of Definition 4.8 is a probability measure. It is the finite independent product of uniform occurrence priorities, a uniform cutoff on [1−ε/2,1], and exponential literal shifts at the positive rate ε/(2bΓ). This verifies normalization of the random input; output-event measurability and algorithmic guarantees are separate.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Definition 4.8, p. 19, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.bijunctive_seed_is_probability {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (bijunctiveSeedMeasure rep I ε) := by sorry
