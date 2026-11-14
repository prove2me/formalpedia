-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_score_compare_measurable
-- name    : StabilityDichotomies.Bijunctive.score_compare_measurable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:18:28.942209+00:00
-- url     : https://prove2.me/theorems/d23a4aa7-9d33-4040-a2b3-e2bda207a5b7
-- title:
--   A literal-score comparison is measurable in the shifts
-- statement:
--   For fixed graph and feasibility subinstances, the event that one literal score strictly exceeds another is measurable as a function of the finite vector of shifts.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Definition 4.8 and proof of Theorem 4.9.

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
open scoped Classical BigOperators
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem StabilityDichotomies.Bijunctive.score_compare_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (a b : Literal V) :
    MeasurableSet {δ : Literal V → ℝ | literalScore rep G F δ b < literalScore rep G F δ a} := by
  sorry
