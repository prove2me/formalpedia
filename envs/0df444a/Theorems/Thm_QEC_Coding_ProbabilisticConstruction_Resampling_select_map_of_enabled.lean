-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_select_map_of_enabled
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.select_map_of_enabled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:32:47.483896+00:00
-- url     : https://prove2.me/theorems/3390c5ea-0200-4b0a-9350-b4c520f114eb
-- title:
--   Resampling: select map of enabled
-- statement:
--   Inserting disabled labels preserves the original priority selection exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L47-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L47-L68

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
variable {W I K : Type*} [Fintype I] [LinearOrder I] [Fintype K] [LinearOrder K]
variable (B : I → Set W) (C : K → Set W)
variable [∀ i, DecidablePred (· ∈ B i)] [∀ k, DecidablePred (· ∈ C k)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.select_map_of_enabled (f : I → K)
    (hle : ∀ i j, f i ≤ f j ↔ i ≤ j)
    (hbad : ∀ i w, w ∈ C (f i) ↔ w ∈ B i)
    (henabled : ∀ k w, w ∈ C k → ∃ i, f i = k) (w : W) :
    (select B w).map f = select C w := by sorry
