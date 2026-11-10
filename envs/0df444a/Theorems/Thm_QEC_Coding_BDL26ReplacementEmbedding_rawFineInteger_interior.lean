-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawFineInteger_interior
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rawFineInteger_interior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:50:47.906713+00:00
-- url     : https://prove2.me/theorems/0dc94a8a-92b2-452b-bf15-0ecf11b89d60
-- title:
--   BDL26 Replacement Embedding: raw Fine Integer interior
-- statement:
--   The BDL26 Replacement Embedding construction uses the raw Fine Integer interior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2466-L2469
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2466-L2469

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rawFineInteger_interior (S : OddScale) (i : Fin S.half)
    (a : BDL26FiniteTannerSquare.Two) :
    rawFineInteger S (.inl (i, a)) = 2 * (i.val : ℤ) + a.val := by sorry
