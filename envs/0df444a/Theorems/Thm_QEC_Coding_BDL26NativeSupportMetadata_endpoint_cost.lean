-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_endpoint_cost
-- name    : QEC.Coding.BDL26NativeSupportMetadata.endpoint_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:46:15.209488+00:00
-- url     : https://prove2.me/theorems/f60e4d01-eeab-4438-9f2f-8b9cbf36a99e
-- title:
--   BDL26 Native Support Metadata: endpoint cost
-- statement:
--   The BDL26 Native Support Metadata construction uses the endpoint cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L138-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L138-L153

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

theorem QEC.Coding.BDL26NativeSupportMetadata.endpoint_cost (F : Frame) (V triangles : List Code) (c : Code) :
    (endpointQ F V triangles c).operations≤44*triangles.length+2*F.faces.length+132*V.length+45 ∧
    (endpointQ F V triangles c).allocations≤triangles.length+3*V.length+6 := by sorry
