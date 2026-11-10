-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_active_before_haltTime
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.active_before_haltTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:27:32.771198+00:00
-- url     : https://prove2.me/theorems/74621500-50e2-4ab1-a5e0-987859b573f2
-- title:
--   Resampling: active before halt Time
-- statement:
--   The Resampling construction uses the active before halt Time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L67-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L67-L74

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.active_before_haltTime (R : Table (X := X)) (h : Halts vars bad R)
    (n : ℕ) (hn : n < haltTime vars bad R) : ∃ i, selected vars bad R n = some i := by sorry
