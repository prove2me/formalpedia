-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_tannerTrianglePoint_glue_qz
-- name    : QEC.Coding.BDL26ReplacementEmbedding.tannerTrianglePoint_glue_qz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T21:31:54.319249+00:00
-- url     : https://prove2.me/theorems/db192dde-2ffc-42c2-ae6b-59f615c91ae0
-- title:
--   BDL26 Replacement Embedding: tanner Triangle Point glue qz
-- statement:
--   Actual shared Q-Z labels give the dual boundary agreement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3403-L3407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3403-L3407

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.tannerTrianglePoint_glue_qz (P : TannerSquarePresentation) (J : Vertex P → E)
    (f g : P.Face) (i j : BDL26FiniteTannerSquare.Two)
    (h : faceQZEdge P f i = faceQZEdge P g j) (t : ℝ) :
    tannerTrianglePoint P J f i (1 - t) t = tannerTrianglePoint P J g j (1 - t) t := by sorry
