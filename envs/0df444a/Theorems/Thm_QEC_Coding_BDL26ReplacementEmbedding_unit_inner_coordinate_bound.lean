-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_unit_inner_coordinate_bound
-- name    : QEC.Coding.BDL26ReplacementEmbedding.unit_inner_coordinate_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:34:22.432066+00:00
-- url     : https://prove2.me/theorems/e84b99c8-f103-4529-9927-cac3f8559117
-- title:
--   BDL26 Replacement Embedding: unit inner coordinate bound
-- statement:
--   Unit directions turn an actual ball condition into a coordinate bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1373-L1379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1373-L1379

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

theorem QEC.Coding.BDL26ReplacementEmbedding.unit_inner_coordinate_bound (e o z p : E) (he : ‖e‖ = 1)
    (hp : dist p z ≤ 2) : |⟪e, p - o⟫_ℝ - ⟪e, z - o⟫_ℝ| ≤ 2 := by sorry
