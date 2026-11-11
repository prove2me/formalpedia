-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rzVertexPoint_hits
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rzVertexPoint_hits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:41:39.570656+00:00
-- url     : https://prove2.me/theorems/61d1dcd8-7d6c-4d06-9bc1-a440b5c35503
-- title:
--   BDL26 Replacement Embedding: rz Vertex Point hits
-- statement:
--   Compare hit families without reducing either packaged finite enumeration.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3464-L3471
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3464-L3471

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rzVertexPoint_hits (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (region : Set E) :
    familyHits (tannerFaceImage (BDL26RZLocalReplacement.rzReplacementPresentation P A S)
      (rzVertexPoint P A S J)) region = familyHits (rzFaceImage P A S J) region := by sorry
