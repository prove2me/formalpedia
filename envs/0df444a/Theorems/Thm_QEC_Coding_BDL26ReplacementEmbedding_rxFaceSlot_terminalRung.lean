-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_terminalRung
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_terminalRung
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:36:58.929728+00:00
-- url     : https://prove2.me/theorems/cd5d3141-cef0-4f72-8cf0-87d8669517da
-- title:
--   BDL26 Replacement Embedding: rx Face Slot terminal Rung
-- statement:
--   The actual terminal rung has the same unique original ordered corner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1719-L1727
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1719-L1727

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_terminalRung (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (terminalRungFace P S f side copy) =
      (f, .inr (.inl (side, .inr 0, copy))) := by sorry
