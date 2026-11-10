-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_halts_and_output_good_ae
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.halts_and_output_good_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:27:28.201465+00:00
-- url     : https://prove2.me/theorems/9db3c254-aa2d-4aac-bd18-41c31f094d24
-- title:
--   Resampling: halts and output good ae
-- statement:
--   The actual product-table resampling algorithm halts and returns a good assignment almost surely.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L161-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L161-L165

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
variable (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
variable (hcrit : ∀ i, eventProbability vars ν bad i ≤
  x i * ∏ j ∈ (supportGraph vars).neighborFinset i, (1 - x j))
include hbad hx0 hx1 hcrit

theorem QEC.Coding.ProbabilisticConstruction.Resampling.halts_and_output_good_ae :
    ∀ᵐ R ∂tableLaw ν, Halts vars bad R ∧ ∀ i, output vars bad R ∉ localEvent vars bad i := by sorry
