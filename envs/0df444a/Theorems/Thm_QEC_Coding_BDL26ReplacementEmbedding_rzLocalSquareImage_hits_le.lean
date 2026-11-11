-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzLocalSquareImage_hits_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzLocalSquareImage_hits_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:44:47.662218+00:00
-- url     : https://prove2.me/theorems/e23db6b6-ba0f-4577-9add-9a8521c8cff7
-- title:
--   BDL26 Replacement Embedding: rz Local Square Image hits le
-- statement:
--   The BDL26 Replacement Embedding construction uses the rz Local Square Image hits le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3777-L3781
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3777-L3781

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzLocalSquareImage_hits_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (region : Set E) :
    (familyHits (rzLocalSquareImage P A S J z) region).card ≤
      (familyHits (rzFaceImage P A S J) region).card := by sorry
