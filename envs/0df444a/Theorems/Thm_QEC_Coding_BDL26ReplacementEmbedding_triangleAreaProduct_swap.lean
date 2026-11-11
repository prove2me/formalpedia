-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleAreaProduct_swap
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangleAreaProduct_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:35:32.903833+00:00
-- url     : https://prove2.me/theorems/4156c2f6-caf0-4ddd-9acf-e14d52ab9290
-- title:
--   BDL26 Replacement Embedding: triangle Area Product swap
-- statement:
--   The BDL26 Replacement Embedding construction uses the triangle Area Product swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1497-L1504
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1497-L1504

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

theorem QEC.Coding.BDL26ReplacementEmbedding.triangleAreaProduct_swap (b c : E) :
    triangleAreaProduct b c = triangleAreaProduct c b := by sorry
