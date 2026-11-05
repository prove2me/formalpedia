-- Prove2me | Theorems.Thm_ProbabilityTheory_charFun_poissonMeasure_eq
-- name    : ProbabilityTheory.charFun_poissonMeasure_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:54:32.362107+00:00
-- url     : https://prove2.me/theorems/f9075f41-5d0f-41c0-9d8e-4071de467fc3
-- title:
--   Characteristic function of the real pushforward of a Poisson distribution (LeanLevy source)
-- statement:
--   The characteristic function of the real pushforward of a Poisson measure of rate r equals exp(r(exp(iξ)-1)). This is the exact LeanLevy source theorem, an immediate consequence of the pinned Mathlib characteristic function identity.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/Probability/Poisson.lean original theorem around lines 229-233.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Probability_Characteristic

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

theorem ProbabilityTheory.charFun_poissonMeasure_eq (r : ℝ≥0) (ξ : ℝ) :
    charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
    cexp (↑(r : ℝ) * (cexp (↑ξ * I) - 1)) := by sorry
