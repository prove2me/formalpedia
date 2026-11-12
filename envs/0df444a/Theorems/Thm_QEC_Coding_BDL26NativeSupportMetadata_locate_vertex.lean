-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_locate_vertex
-- name    : QEC.Coding.BDL26NativeSupportMetadata.locate_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:50:16.582391+00:00
-- url     : https://prove2.me/theorems/ae7c0258-50aa-4266-8cd2-c1b35b13a56b
-- title:
--   BDL26 Native Support Metadata: locate vertex
-- statement:
--   The BDL26 Native Support Metadata construction uses the locate vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L544-L554
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeSupportMetadata.lean#L544-L554

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

theorem QEC.Coding.BDL26NativeSupportMetadata.locate_vertex (S : OddScale) (n : ℕ) (v : Vertex (P S n)) :
    (locateQ (vertexCode S n v) (V S n)).value=
      some (BDL26NativePresentationGenerator.generatedVertexIndex S n v) := by sorry
