-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_lower_last_normalized
-- name    : QEC.Coding.BDL26ReplacementEmbedding.lower_last_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:50:48.821846+00:00
-- url     : https://prove2.me/theorems/5a286e7e-a16b-4e55-9938-8bcb1bf9db71
-- title:
--   BDL26 Replacement Embedding: lower last normalized
-- statement:
--   The BDL26 Replacement Embedding construction uses the lower last normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L465-L468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L465-L468

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
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.lower_last_normalized (S : OddScale) :
    ((lower S (lastStrip S)).val : ℝ) / S.ell = contractionRatio S := by sorry
