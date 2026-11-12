-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_rows_cost
-- name    : QEC.Coding.BDL26NativeSupportMetadata.atlas_rows_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:44:48.31725+00:00
-- url     : https://prove2.me/theorems/ce187f44-4b95-4c4d-9a59-95162e4905e9
-- title:
--   BDL26 Native Support Metadata: atlas rows cost
-- statement:
--   The BDL26 Native Support Metadata construction uses the atlas rows cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L166-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L166-L184

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

theorem QEC.Coding.BDL26NativeSupportMetadata.atlas_rows_cost (F : Frame) (V triangles : List Code) :
    (atlasRowsQ F V triangles).operations≤
      triangles.length*(44*triangles.length+2*F.faces.length+132*V.length+50) ∧
    (atlasRowsQ F V triangles).allocations≤triangles.length*(triangles.length+3*V.length+8) := by sorry
