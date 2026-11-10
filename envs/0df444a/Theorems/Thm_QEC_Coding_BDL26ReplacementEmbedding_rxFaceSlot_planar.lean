-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rxFaceSlot_planar
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_planar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:36:58.222771+00:00
-- url     : https://prove2.me/theorems/3cc6bacd-07a8-4071-90e1-84e4da2c5dac
-- title:
--   BDL26 Replacement Embedding: rx Face Slot planar
-- statement:
--   The actual planar quadrant has its original face owner and retained endpoint bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1696-L1699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1696-L1699

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rxFaceSlot_planar (P : TannerSquarePresentation) (S : OddScale) (f : P.Face)
    (i j : Fin S.half) (copy a b : BDL26FiniteTannerSquare.Two) :
    rxFaceSlotEquiv P S (.inl ⟨P.faceX f, .inl (copy, oldFaceInXStar P f, i, j), a, b⟩) =
      (f, .inl (.inl ((copy, i, j), a, b))) := by sorry
