-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_dedup_length
-- name    : QEC.Coding.BDL26NativeSupportMetadata.dedup_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:27:49.500766+00:00
-- url     : https://prove2.me/theorems/a327cccf-0d5d-4acb-a1ae-53c8269e3a36
-- title:
--   BDL26 Native Support Metadata: dedup length
-- statement:
--   The BDL26 Native Support Metadata construction uses the dedup length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L276-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L276-L283

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

theorem QEC.Coding.BDL26NativeSupportMetadata.dedup_length {A : Type*} [DecidableEq A] (L : List A) :
    (dedupQ L).value.length≤L.length := by sorry
