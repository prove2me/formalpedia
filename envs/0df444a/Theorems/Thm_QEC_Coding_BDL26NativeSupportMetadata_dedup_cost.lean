-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_dedup_cost
-- name    : QEC.Coding.BDL26NativeSupportMetadata.dedup_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:46:06.445534+00:00
-- url     : https://prove2.me/theorems/7387dedf-f929-4dd6-9e49-0d7c7d8b544d
-- title:
--   BDL26 Native Support Metadata: dedup cost
-- statement:
--   The BDL26 Native Support Metadata construction uses the dedup cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L285-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L285-L295

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

theorem QEC.Coding.BDL26NativeSupportMetadata.dedup_cost {A : Type*} [DecidableEq A] (L : List A) :
    (dedupQ L).operations≤L.length*(2*L.length+4)+1 ∧
    (dedupQ L).allocations≤L.length := by sorry
