-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_vertex_handle
-- name    : QEC.Coding.BDL26NativeSupportMetadata.vertex_handle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:50:42.370553+00:00
-- url     : https://prove2.me/theorems/5f83203f-85ab-4f3d-8262-c881da7d258d
-- title:
--   BDL26 Native Support Metadata: vertex handle
-- statement:
--   The BDL26 Native Support Metadata construction uses the vertex handle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L539-L542
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L539-L542

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
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeSupportMetadata.vertex_handle (S : OddScale) (n : ℕ) (v : Vertex (P S n)) :
    (BDL26NativePresentationGenerator.handleQ (vertexCode S n v) (V S n)).1=
      (BDL26NativePresentationGenerator.generatedVertexIndex S n v).val := by sorry
