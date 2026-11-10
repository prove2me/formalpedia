-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldTriangleImage_transpose
-- name    : QEC.Coding.BDL26ReplacementEmbedding.oldTriangleImage_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:40:24.865892+00:00
-- url     : https://prove2.me/theorems/81c02716-e450-427c-b792-bbaf60ed38ff
-- title:
--   BDL26 Replacement Embedding: old Triangle Image transpose
-- statement:
--   Transposing X and Z preserves every incoming triangle label and its geometric image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2868-L2877
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2868-L2877

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

theorem QEC.Coding.BDL26ReplacementEmbedding.oldTriangleImage_transpose (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (side : BDL26FiniteTannerSquare.Two) :
    oldTriangleImage (transposePresentation P) (transposePointMap P J) (f, side) =
      oldTriangleImage P J (f, side) := by sorry
