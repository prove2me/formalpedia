-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_refresh_success
-- name    : QEC.Coding.BDL26NativeSupportMetadata.refresh_success
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:50:30.766766+00:00
-- url     : https://prove2.me/theorems/1550b265-90db-4763-8ee1-f71f7f720dc6
-- title:
--   BDL26 Native Support Metadata: refresh success
-- statement:
--   The BDL26 Native Support Metadata construction uses the refresh success property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L469-L478
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L469-L478

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N

theorem QEC.Coding.BDL26NativeSupportMetadata.refresh_success (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (trace : List (List (Index S n))) (U : List (Index S n))
    (h : (queryQ S n codes).value=some U) :
    (refreshEventQ S n codes table trace).value=some
      (BDL26NativeStateRows.rowsFor (BDL26NativeStateRows.indices (BDL26NativeStateRows.count S n))
        table (BDL26NativeStateRows.advanceList U
          (BDL26NativeStateRows.traceCounters trace (fun _ => 0)))) := by sorry
