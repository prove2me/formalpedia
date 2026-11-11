-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_tannerTrianglePoint_xq
-- name    : QEC.Coding.BDL26ReplacementEmbedding.tannerTrianglePoint_xq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:42:30.089699+00:00
-- url     : https://prove2.me/theorems/b7496176-b710-4a0e-a36b-04b4d897bcd0
-- title:
--   BDL26 Replacement Embedding: tanner Triangle Point xq
-- statement:
--   Every local triangle agrees with its global X-Q boundary map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3377-L3380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3377-L3380

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

theorem QEC.Coding.BDL26ReplacementEmbedding.tannerTrianglePoint_xq (P : TannerSquarePresentation) (J : Vertex P → E)
    (f : P.Face) (side : BDL26FiniteTannerSquare.Two) (t : ℝ) :
    tannerTrianglePoint P J f side t 0 = xqEdgePoint P J (faceXQEdge P f side) t := by sorry
