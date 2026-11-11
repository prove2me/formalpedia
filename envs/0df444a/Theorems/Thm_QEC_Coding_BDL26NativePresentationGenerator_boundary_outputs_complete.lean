-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_boundary_outputs_complete
-- name    : QEC.Coding.BDL26NativePresentationGenerator.boundary_outputs_complete
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:50:54.098379+00:00
-- url     : https://prove2.me/theorems/2b744262-da6f-4160-8539-9e4ef236a0ab
-- title:
--   BDL26 Native Presentation Generator: boundary outputs complete
-- statement:
--   Actual materialized boundary outputs contain every coefficient used in the full-word laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3584-L3602
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3584-L3602

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation

theorem QEC.Coding.BDL26NativePresentationGenerator.boundary_outputs_complete (S : OddScale) (n : ℕ)
    (v : Fin (runQ S n).1.vertices.length) (e : Fin (runQ S n).1.edges.length)
    (f : Fin (runQ S n).1.frame.nf) :
    (v.val,e.val,(edgeVertexTestQ ((runQ S n).1.edges.get e)
      ((runQ S n).1.vertices.get v)).1)∈(runQ S n).1.boundary1 ∧
    (e.val,f.val,(faceEdgeTestQ (faceAtQ (runQ S n).1.frame.faces f.val).1
      ((runQ S n).1.edges.get e)).1)∈(runQ S n).1.boundary2 := by sorry
