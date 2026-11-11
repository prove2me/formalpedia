-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleGridIndex_injective
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangleGridIndex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:37:41.980872+00:00
-- url     : https://prove2.me/theorems/ba445d57-3e0d-4b1a-a5b3-93a871fbde08
-- title:
--   BDL26 Replacement Embedding: triangle Grid Index injective
-- statement:
--   The BDL26 Replacement Embedding construction uses the triangle Grid Index injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2301-L2308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2301-L2308

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

theorem QEC.Coding.BDL26ReplacementEmbedding.triangleGridIndex_injective (side : BDL26FiniteTannerSquare.Two) :
    Function.Injective (triangleGridIndex side) := by sorry
