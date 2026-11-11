-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_read_missing
-- name    : QEC.Coding.BDL26NativeSupportMetadata.atlas_read_missing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:38:49.749334+00:00
-- url     : https://prove2.me/theorems/f625116a-9138-40df-9e4b-e4963c5dd8a6
-- title:
--   BDL26 Native Support Metadata: atlas read missing
-- statement:
--   The BDL26 Native Support Metadata construction uses the atlas read missing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L225-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L225-L237

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

theorem QEC.Coding.BDL26NativeSupportMetadata.atlas_read_missing {A : Type*} (f : Code → Option A) (c : Code) (L : List Code)
    (hc : c∉L) :
    (atlasReadQ c (L.map (fun a => (a,f a)))).value=none ∧
      (atlasReadQ c (L.map (fun a => (a,f a)))).operations=43*L.length+1 := by sorry
