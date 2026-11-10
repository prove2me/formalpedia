-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_boundaryRectangle
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_boundaryRectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:37:38.051621+00:00
-- url     : https://prove2.me/theorems/363944c7-706d-4feb-a156-f98a8e2f760b
-- title:
--   BDL26 Replacement Embedding: rx Face Slot boundary Rectangle
-- statement:
--   The BDL26 Replacement Embedding construction uses the rx Face Slot boundary Rectangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1737-L1747
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1737-L1747

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_boundaryRectangle (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (boundaryRectangleFace P S f side copy i endpoint) =
      (f, .inl (.inr (side, i, copy, endpoint))) := by sorry
