-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_refresh_cost
-- name    : QEC.Coding.BDL26NativeSupportMetadata.refresh_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:59:39.913204+00:00
-- url     : https://prove2.me/theorems/584ff165-11f7-4dc2-a540-bf2fd7f4c756
-- title:
--   BDL26 Native Support Metadata: refresh cost
-- statement:
--   The BDL26 Native Support Metadata construction uses the refresh cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L480-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L480-L501

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_refresh_cost

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N

theorem QEC.Coding.BDL26NativeSupportMetadata.refresh_cost (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (trace : List (List (Index S n))) :
    (refreshEventQ S n codes table trace).operations≤(queryQ S n codes).operations+
      (BDL26NativeStateRows.executeQ S n table trace).operations+35*BDL26NativeStateRows.count S n+4 ∧
    (refreshEventQ S n codes table trace).allocations≤(queryQ S n codes).allocations+
      (BDL26NativeStateRows.executeQ S n table trace).allocations+2*BDL26NativeStateRows.count S n+1 := by sorry
