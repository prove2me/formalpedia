-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_refresh_failure
-- name    : QEC.Coding.BDL26NativeSupportMetadata.refresh_failure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:57:31.817648+00:00
-- url     : https://prove2.me/theorems/547a1368-402f-4c3b-9127-586d3358f5c3
-- title:
--   BDL26 Native Support Metadata: refresh failure
-- statement:
--   The BDL26 Native Support Metadata construction uses the refresh failure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L461-L467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L461-L467

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

theorem QEC.Coding.BDL26NativeSupportMetadata.refresh_failure (S : OddScale) (n : ℕ) (codes : FourCodes)
    (table : BDL26NativeStateRows.Samples (Index S n))
    (trace : List (List (Index S n))) (h : (queryQ S n codes).value=none) :
    (refreshEventQ S n codes table trace).value=none ∧
    (refreshEventQ S n codes table trace).operations=(queryQ S n codes).operations+2 ∧
    (refreshEventQ S n codes table trace).allocations=(queryQ S n codes).allocations := by sorry
