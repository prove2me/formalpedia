-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedGridPoint_corner_dist
-- name    : QEC.Coding.BDL26ReplacementEmbedding.foldedGridPoint_corner_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:36:15.11414+00:00
-- url     : https://prove2.me/theorems/e737786a-cec3-4d2e-a8dd-5dc5b7f79bb7
-- title:
--   BDL26 Replacement Embedding: folded Grid Point corner dist
-- statement:
--   Every real corner of a fine cell is within one unit of its lower-left anchor.
--   The five hypotheses are exactly sides of the two original triangles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1626-L1688
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1626-L1688

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

theorem QEC.Coding.BDL26ReplacementEmbedding.foldedGridPoint_corner_dist (x q₀ q₁ z : E) {ell : ℝ}
    (hell : 0 < ell) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two)
    (h₀ : ‖q₀ - x‖ ≤ ell) (h₁ : ‖q₁ - x‖ ≤ ell) (hz : ‖z - x‖ ≤ ell)
    (hz₀ : ‖z - q₀‖ ≤ ell) (hz₁ : ‖z - q₁‖ ≤ ell) :
    dist (foldedGridPoint x q₀ q₁ z ell (m + a.val) (n + b.val))
      (foldedGridPoint x q₀ q₁ z ell m n) ≤ 1 := by sorry
