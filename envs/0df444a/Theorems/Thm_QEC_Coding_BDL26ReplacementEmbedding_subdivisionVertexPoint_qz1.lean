-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionVertexPoint_qz1
-- name    : QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_qz1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:30:45.652139+00:00
-- url     : https://prove2.me/theorems/3f5ea8ad-c472-449f-8076-ac0f51c0e8d5
-- title:
--   BDL26 Replacement Embedding: subdivision Vertex Point qz1
-- statement:
--   Actual Q1-Z interior tags lie on the top contracted side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L768-L780
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L768-L780

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

theorem QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_qz1 (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i : Fin (S.half - 1)) :
    subdivisionVertexPoint P S J x (.inr (.inl (xStarFaceQZEdge P x f 1, i))) =
      facePoint P J f.1 (2 * ((i.val : ℝ) + 1) / S.ell) (contractionRatio S) := by sorry
