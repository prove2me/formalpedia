-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_upper_lattice
-- name    : QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_upper_lattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:34:40.497192+00:00
-- url     : https://prove2.me/theorems/c0839dab-e299-46b9-9b53-afb3f3b0488d
-- title:
--   BDL26 Replacement Embedding: folded Square upper lattice
-- statement:
--   The upper chart uses the other actual triangle and the exchanged integer coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1421-L1429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1421-L1429

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

theorem QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_upper_lattice (x q₀ q₁ z : E) {ell : ℝ}
    (hell : 0 < ell) (m n : ℤ) (hmn : m ≤ n) :
    foldedSquare x q₀ q₁ z ((m : ℝ) / ell) ((n : ℝ) / ell) =
      triangleLatticeAnchor x (q₁ - x) (z - x) ell (n - m, m) := by sorry
