-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_endpoint_missing
-- name    : QEC.Coding.BDL26NativeSupportMetadata.endpoint_missing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:53:08.046226+00:00
-- url     : https://prove2.me/theorems/99ae98c9-c896-49c2-bf05-a198d053e096
-- title:
--   BDL26 Native Support Metadata: endpoint missing
-- statement:
--   The BDL26 Native Support Metadata construction uses the endpoint missing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L134-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L134-L136

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

theorem QEC.Coding.BDL26NativeSupportMetadata.endpoint_missing (F : Frame) (V triangles : List Code) (c : Code)
    (hc : c∉triangles) : (endpointQ F V triangles c).value=none := by sorry
