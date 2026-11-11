-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzVertexPoint_faceImage
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzVertexPoint_faceImage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:43:38.25496+00:00
-- url     : https://prove2.me/theorems/c26b8cb8-3ccd-4fc5-ab2b-63c5b8ed7697
-- title:
--   BDL26 Replacement Embedding: rz Vertex Point face Image
-- statement:
--   The BDL26 Replacement Embedding construction uses the rz Vertex Point face Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3448-L3451
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3448-L3451

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzVertexPoint_faceImage (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (f : BDL26RZLocalReplacement.RZFace P S) :
    tannerFaceImage (BDL26RZLocalReplacement.rzReplacementPresentation P A S)
      (rzVertexPoint P A S J) f = rzFaceImage P A S J f := by sorry
