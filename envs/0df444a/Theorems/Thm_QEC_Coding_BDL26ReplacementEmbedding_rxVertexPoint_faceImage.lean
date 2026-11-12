-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxVertexPoint_faceImage
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxVertexPoint_faceImage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T21:31:38.103593+00:00
-- url     : https://prove2.me/theorems/f4787aaf-48bb-435f-836e-c6c3ae6fecbd
-- title:
--   BDL26 Replacement Embedding: rx Vertex Point face Image
-- statement:
--   The resulting square realization is definitionally the actual materialized face image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3435-L3438
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3435-L3438

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.rxVertexPoint_faceImage (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : RXFace P S) :
    tannerFaceImage (rxReplacementPresentation P S) (rxVertexPoint P S J) f =
      rxFaceImage P S J f := by sorry
