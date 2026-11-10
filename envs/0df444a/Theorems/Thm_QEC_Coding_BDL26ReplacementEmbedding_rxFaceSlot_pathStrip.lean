-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_pathStrip
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_pathStrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:07:17.365202+00:00
-- url     : https://prove2.me/theorems/c694becc-81e2-4067-8c78-7ded8f411c4f
-- title:
--   BDL26 Replacement Embedding: rx Face Slot path Strip
-- statement:
--   The actual path strip is matched to its unique face by perfect pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1707-L1716
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1707-L1716

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_pathStrip (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (side copy : BDL26FiniteTannerSquare.Two) (i : Fin S.half)
    (endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (pathStripFace P S f side copy i endpoint) =
      (f, .inr (.inl (side, .inl (copy, i), endpoint))) := by sorry
