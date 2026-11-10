-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_expected_totalSteps_sq_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.expected_totalSteps_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:38:22.893202+00:00
-- url     : https://prove2.me/theorems/5740e07c-0f69-44bf-92e6-e422293728f3
-- title:
--   Resampling: expected total Steps sq le
-- statement:
--   Under the actual uniform event-probability and support-degree bounds, the
--   unchanged product-table resampling process has an explicit finite second moment.
--   No halting, tail, local-lemma or execution certificate is an input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/StrictSlackMoments.lean#L353-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/StrictSlackMoments.lean#L353-L371

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
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
include hbad

theorem QEC.Coding.ProbabilisticConstruction.Resampling.expected_totalSteps_sq_le (D : ℕ)
    (hdegree : ∀ i, ((supportGraph vars).neighborFinset i).card ≤ D)
    (hprob : ∀ i, eventProbability vars ν bad i ≤ 1/(4*((D : ℝ)+1))) :
    (∫⁻ R, (totalSteps vars bad R)^2 ∂tableLaw ν) ≤
      (2*(Fintype.card I)^2*(D+2)^2 : ℕ) := by sorry
