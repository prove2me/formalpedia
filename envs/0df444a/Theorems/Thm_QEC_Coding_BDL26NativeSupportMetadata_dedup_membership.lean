-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_dedup_membership
-- name    : QEC.Coding.BDL26NativeSupportMetadata.dedup_membership
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:54:53.336891+00:00
-- url     : https://prove2.me/theorems/6bdab599-a7ec-4c6b-9eb2-c7211415b1a9
-- title:
--   BDL26 Native Support Metadata: dedup membership
-- statement:
--   The BDL26 Native Support Metadata construction uses the dedup membership property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L248-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L248-L262

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

theorem QEC.Coding.BDL26NativeSupportMetadata.dedup_membership {A : Type*} [DecidableEq A] (L : List A) (a : A) :
    a∈(dedupQ L).value ↔ a∈L := by sorry
