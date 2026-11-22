-- Prove2me | Theorems.Thm_UniformDelta
-- name    : UniformDelta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:41.868795+00:00
-- url     : https://prove2.me/theorems/84b1c37d-ff97-46ac-8833-1ffed123a12f
-- title:
--   Uniform Delta: Uniform Delta
-- statement:
--   Uniform separation from the zero set of a continuous nonnegative functional on
--   a compact set.  If `F` is continuous and nonnegative on a compact `K` and `U` is an
--   open set containing the zero set `{z ∈ K | F z = 0}`, then some whole sublevel set
--   `{z ∈ K | F z ≤ δ}` with `δ > 0` is already contained in `U`.
--
--   This is the compactness step the paper uses to turn a cover of the critical members
--   of its family into a bound on the size of the gradient at the origin: the paper
--   argues it by contradiction through a convergent subsequence, and the direct form
--   here is that `F` attains a positive minimum on the compact set `K \ U`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/UniformDelta.lean#L12-L34
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/UniformDelta.lean#L12-L34

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_UniformDelta
set_option autoImplicit false

theorem UniformDelta (X : Type) [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (F : X → ℝ)
    (hF : ContinuousOn F K) (hFnn : ∀ z ∈ K, 0 ≤ F z)
    (U : Set X) (hU : IsOpen U) (hsub : {z ∈ K | F z = 0} ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ {z ∈ K | F z ≤ δ} ⊆ U := by sorry
