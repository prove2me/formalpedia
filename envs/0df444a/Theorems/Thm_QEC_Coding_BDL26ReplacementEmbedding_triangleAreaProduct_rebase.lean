-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_triangleAreaProduct_rebase
-- name    : QEC.Coding.BDL26ReplacementEmbedding.triangleAreaProduct_rebase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:35:57.970251+00:00
-- url     : https://prove2.me/theorems/85850c99-b2a5-4716-b878-271289d8d6b5
-- title:
--   BDL26 Replacement Embedding: triangle Area Product rebase
-- statement:
--   The BDL26 Replacement Embedding construction uses the triangle Area Product rebase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1506-L1515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1506-L1515

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

theorem QEC.Coding.BDL26ReplacementEmbedding.triangleAreaProduct_rebase (b c : E) :
    triangleAreaProduct b c = triangleAreaProduct (c - b) (-b) := by sorry
