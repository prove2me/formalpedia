-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_foldedSquare_mem_lower_triangle
-- name    : QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_mem_lower_triangle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:32:45.280171+00:00
-- url     : https://prove2.me/theorems/6bc9d1c6-25c9-4591-9e46-026404cb1fe5
-- title:
--   BDL26 Replacement Embedding: folded Square mem lower triangle
-- statement:
--   The lower affine chart lies in the actual incoming triangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1246-L1254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1246-L1254

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

theorem QEC.Coding.BDL26ReplacementEmbedding.foldedSquare_mem_lower_triangle (x q₀ q₁ z : E) {u v : ℝ}
    (hu : u ≤ 1) (hv : 0 ≤ v) (hvu : v ≤ u) :
    foldedSquare x q₀ q₁ z u v ∈ convexHull ℝ {x, q₀, z} := by sorry
