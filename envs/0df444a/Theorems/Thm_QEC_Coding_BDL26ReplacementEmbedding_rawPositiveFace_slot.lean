-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawPositiveFace_slot
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rawPositiveFace_slot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:37:46.001039+00:00
-- url     : https://prove2.me/theorems/945d6d5b-dc2e-42c3-97c8-6116b29e096b
-- title:
--   BDL26 Replacement Embedding: raw Positive Face slot
-- statement:
--   Exact owner/slot correspondence for the constructed positive family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2235-L2243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2235-L2243

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
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.rawPositiveFace_slot (P : TannerSquarePresentation) (S : OddScale)
    (f : P.Face) (c : RawPositiveCell S) :
    rxFaceSlotEquiv P S (rawPositiveFace P S f c) =
      (f, rawFlatToPatchSlot S (.inl c)) := by sorry
