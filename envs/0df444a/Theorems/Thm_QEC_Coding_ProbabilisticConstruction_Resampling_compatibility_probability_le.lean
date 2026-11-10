-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_compatibility_probability_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.compatibility_probability_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:20:35.331198+00:00
-- url     : https://prove2.me/theorems/a49fdce6-7523-4185-9af1-d2748c51dff8
-- title:
--   Resampling: compatibility probability le
-- statement:
--   A compatible witness has at most the product probability of its labeled events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L113-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessCompatibility.lean#L113-L130

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryTimes
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessCompatibility
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (vars : I → Finset V)
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))

theorem QEC.Coding.ProbabilisticConstruction.Resampling.compatibility_probability_le (hbad : ∀ i, MeasurableSet (bad i))
    (root : I) (P : Finset (List I)) :
    tableLaw ν (compatible vars bad root P) ≤
      ∏ p : P, (Measure.pi ν) (localEvent vars bad (pathLabel root p.val)) := by sorry
