-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_subdivisionVerticalEdge_midpoint
-- name    : QEC.Coding.BDL26ReplacementEmbedding.subdivisionVerticalEdge_midpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:31:28.988987+00:00
-- url     : https://prove2.me/theorems/6f136711-48c6-498c-9e20-a96c78ceca66
-- title:
--   BDL26 Replacement Embedding: subdivision Vertical Edge midpoint
-- statement:
--   Actual vertical subdivision endpoints also stay within one old affine triangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L906-L942
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L906-L942

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

theorem QEC.Coding.BDL26ReplacementEmbedding.subdivisionVerticalEdge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (f : XStarFace P x)
    (i : Fin (S.half + 1)) (j : Fin S.half) :
    (1 / 2 : ℝ) •
      (subdivisionVertexPoint P S J x
        (subdivisionEdgeStart P x S (subdivisionVerticalEdge P x S f i j)) +
       subdivisionVertexPoint P S J x
        (subdivisionEdgeEnd P x S (subdivisionVerticalEdge P x S f i j))) =
      facePoint P J f.1 (2 * (i.val : ℝ) / S.ell)
        ((2 * (j.val : ℝ) + 1) / S.ell) := by sorry
