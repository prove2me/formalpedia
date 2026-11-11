-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_tannerTrianglePoint_diagonal
-- name    : QEC.Coding.BDL26ReplacementEmbedding.tannerTrianglePoint_diagonal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T21:31:05.408194+00:00
-- url     : https://prove2.me/theorems/663fc3d2-6b34-4963-af50-d4f162d428ad
-- title:
--   BDL26 Replacement Embedding: tanner Triangle Point diagonal
-- statement:
--   Both charts agree on the auxiliary X-Z diagonal, even when the square is folded.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3390-L3393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3390-L3393

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

theorem QEC.Coding.BDL26ReplacementEmbedding.tannerTrianglePoint_diagonal (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (t : ℝ) :
    tannerTrianglePoint P J f 0 0 t = tannerTrianglePoint P J f 1 0 t := by sorry
