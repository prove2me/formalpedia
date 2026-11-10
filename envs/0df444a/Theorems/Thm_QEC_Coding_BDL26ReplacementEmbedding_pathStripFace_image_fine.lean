-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_pathStripFace_image_fine
-- name    : QEC.Coding.BDL26ReplacementEmbedding.pathStripFace_image_fine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:39:33.370013+00:00
-- url     : https://prove2.me/theorems/3aea9f32-d758-4c4e-8760-585f4842f6be
-- title:
--   BDL26 Replacement Embedding: path Strip Face image fine
-- statement:
--   The last column has the actual swapped Q-corner order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2503-L2520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2503-L2520

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

theorem QEC.Coding.BDL26ReplacementEmbedding.pathStripFace_image_fine (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two)
    (i : Fin S.half) (a : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (pathStripFace P S f 0 copy i a) =
      fineQuadrantImage P S J f (2 * S.half) (2 * i.val + a.val) 0 a := by sorry
