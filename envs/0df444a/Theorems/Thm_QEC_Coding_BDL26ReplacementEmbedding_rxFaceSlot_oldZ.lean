-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_oldZ
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_oldZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:07:12.279842+00:00
-- url     : https://prove2.me/theorems/5871bb72-6d3b-4e15-8c32-fdcecdcd0c21
-- title:
--   BDL26 Replacement Embedding: rx Face Slot old Z
-- statement:
--   The actual old-Z quadrant retains its owner and coincident copy label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1702-L1704
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1702-L1704

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_oldZ (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (.inr (.inr (f, copy))) = (f, .inr (.inr copy)) := by sorry
