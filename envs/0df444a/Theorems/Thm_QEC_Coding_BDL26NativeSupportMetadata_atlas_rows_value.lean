-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_rows_value
-- name    : QEC.Coding.BDL26NativeSupportMetadata.atlas_rows_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:46:47.388535+00:00
-- url     : https://prove2.me/theorems/d3e67219-614e-4383-ba10-4e433d84fdc7
-- title:
--   BDL26 Native Support Metadata: atlas rows value
-- statement:
--   The BDL26 Native Support Metadata construction uses the atlas rows value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L161-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L161-L164

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

theorem QEC.Coding.BDL26NativeSupportMetadata.atlas_rows_value (F : Frame) (V triangles : List Code) :
    (atlasRowsQ F V triangles).value=
      triangles.map (fun c => (c,(endpointQ F V triangles c).value)) := by sorry
