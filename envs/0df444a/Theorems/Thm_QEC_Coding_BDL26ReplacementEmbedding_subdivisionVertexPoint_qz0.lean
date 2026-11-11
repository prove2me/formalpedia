-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionVertexPoint_qz0
-- name    : QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_qz0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:30:55.674864+00:00
-- url     : https://prove2.me/theorems/336189f7-6eff-46f4-9ac7-b3aab02d35e9
-- title:
--   BDL26 Replacement Embedding: subdivision Vertex Point qz0
-- statement:
--   Actual Q0-Z interior tags lie on the right contracted side, with shared endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L753-L765
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L753-L765

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

theorem QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_qz0 (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i : Fin (S.half - 1)) :
    subdivisionVertexPoint P S J x (.inr (.inl (xStarFaceQZEdge P x f 0, i))) =
      facePoint P J f.1 (contractionRatio S) (2 * ((i.val : ℝ) + 1) / S.ell) := by sorry
