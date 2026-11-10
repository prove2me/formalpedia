-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionVertexPoint_xq0
-- name    : QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_xq0
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:30:11.621199+00:00
-- url     : https://prove2.me/theorems/6f263a77-b488-4921-9040-de1b89410f3f
-- title:
--   BDL26 Replacement Embedding: subdivision Vertex Point xq0
-- statement:
--   Every actual X-Q0 interior tag has the horizontal contracted-grid coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L721-L734
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L721-L734

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

theorem QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_xq0 (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i : Fin (S.half - 1)) :
    subdivisionVertexPoint P S J x (.inr (.inl (xStarFaceXQEdge P x f 0, i))) =
      facePoint P J f.1 (2 * ((i.val : ℝ) + 1) / S.ell) 0 := by sorry
