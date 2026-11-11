-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_read_map
-- name    : QEC.Coding.BDL26NativeSupportMetadata.atlas_read_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:51:43.341252+00:00
-- url     : https://prove2.me/theorems/98ed8e92-eefb-4869-8fdd-4e742dfa5717
-- title:
--   BDL26 Native Support Metadata: atlas read map
-- statement:
--   The BDL26 Native Support Metadata construction uses the atlas read map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L215-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L215-L223

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

theorem QEC.Coding.BDL26NativeSupportMetadata.atlas_read_map {A : Type*} (f : Code → Option A) (c : Code) (L : List Code)
    (hc : c∈L) : (atlasReadQ c (L.map (fun a => (a,f a)))).value=f c := by sorry
