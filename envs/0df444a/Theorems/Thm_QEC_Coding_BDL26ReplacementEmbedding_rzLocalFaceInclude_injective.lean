-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzLocalFaceInclude_injective
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzLocalFaceInclude_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:44:18.908309+00:00
-- url     : https://prove2.me/theorems/4b753305-b9cf-4eb4-a111-cc06b2563013
-- title:
--   BDL26 Replacement Embedding: rz Local Face Include injective
-- statement:
--   The BDL26 Replacement Embedding construction uses the rz Local Face Include injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3766-L3769
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3766-L3769

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.rzLocalFaceInclude_injective (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    Function.Injective (rzLocalFaceInclude P S z) := by sorry
