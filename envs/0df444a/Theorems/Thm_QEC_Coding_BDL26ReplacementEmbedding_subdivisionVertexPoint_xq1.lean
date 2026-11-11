-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionVertexPoint_xq1
-- name    : QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_xq1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:30:33.158075+00:00
-- url     : https://prove2.me/theorems/52e19fc4-2237-4d7e-a63f-a588011023fc
-- title:
--   BDL26 Replacement Embedding: subdivision Vertex Point xq1
-- statement:
--   Every actual X-Q1 interior tag has the vertical contracted-grid coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L737-L750
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L737-L750

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

theorem QEC.Coding.BDL26ReplacementEmbedding.subdivisionVertexPoint_xq1 (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x) (i : Fin (S.half - 1)) :
    subdivisionVertexPoint P S J x (.inr (.inl (xStarFaceXQEdge P x f 1, i))) =
      facePoint P J f.1 0 (2 * ((i.val : ℝ) + 1) / S.ell) := by sorry
