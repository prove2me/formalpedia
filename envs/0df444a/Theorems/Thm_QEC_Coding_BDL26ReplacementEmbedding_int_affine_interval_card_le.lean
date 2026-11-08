-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_int_affine_interval_card_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.int_affine_interval_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:38:50.804467+00:00
-- url     : https://prove2.me/theorems/b60de95a-9e99-4003-8fc6-658ba556a9a2
-- title:
--   BDL26 Replacement Embedding: int affine interval card le
-- statement:
--   Count lattice points in a translated real interval; no separation certificate is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L258-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean#L258-L271

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
open scoped BigOperators

theorem QEC.Coding.BDL26ReplacementEmbedding.int_affine_interval_card_le (s : Finset ℤ) {spacing center radius : ℝ}
    (hspacing : 0 < spacing) (hradius : 0 ≤ radius)
    (hmem : ∀ z ∈ s, |spacing * (z : ℝ) - center| ≤ radius) :
    (s.card : ℝ) ≤ 2 * radius / spacing + 1 := by sorry
