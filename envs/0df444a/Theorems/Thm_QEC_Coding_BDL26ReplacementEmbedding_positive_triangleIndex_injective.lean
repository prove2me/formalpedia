-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_positive_triangleIndex_injective
-- name    : QEC.Coding.BDL26ReplacementEmbedding.positive_triangleIndex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:41:01.060888+00:00
-- url     : https://prove2.me/theorems/405790fd-3b14-4bf2-977d-fc771ff7ee44
-- title:
--   BDL26 Replacement Embedding: positive triangle Index injective
-- statement:
--   Actual positive cells inject into their copy label and the selected triangle lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2621-L2636
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2621-L2636

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

theorem QEC.Coding.BDL26ReplacementEmbedding.positive_triangleIndex_injective (S : OddScale)
    (side : BDL26FiniteTannerSquare.Two) :
    Function.Injective (fun c : PositiveCell S =>
      (c.1, triangleGridIndex side (c.2.1.val, c.2.2.val))) := by sorry
