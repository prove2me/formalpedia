-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_locate_cost
-- name    : QEC.Coding.BDL26NativeSupportMetadata.locate_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:43:52.173397+00:00
-- url     : https://prove2.me/theorems/552d4ff9-b809-49ae-80f0-9f89fc95a29f
-- title:
--   BDL26 Native Support Metadata: locate cost
-- statement:
--   The BDL26 Native Support Metadata construction uses the locate cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L67-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L67-L78

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

theorem QEC.Coding.BDL26NativeSupportMetadata.locate_cost (c : Code) (L : List Code) :
    (locateQ c L).operations≤44*L.length+1 ∧ (locateQ c L).allocations≤L.length := by sorry
