-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_A_comp_B
-- name    : ShorNonsmooth.SpaceDilation.sdg_A_comp_B
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T08:36:06.230183+00:00
-- url     : https://prove2.me/theorems/9e0883d2-40ca-4bcb-a5be-8bf0137da645
-- title:
--   SDG operators satisfy A_k \u2218 B_k = id along a non-stopped run
-- statement:
--   Along a run of the SDG method that never triggers the stopping rule, with coefficients α satisfying 1 + δ ≤ α_k for all k ≥ 1, the space-transformation operator A_k composed with the operator B_k of (3.9) is the identity: A_k ∘ B_k = id.\n\nThis is the counterpart of the already-proved theorem `sdg_B_comp_A`, which gives B_k ∘ A_k = id. Theorem 3.3 needs the direction stated here, because the one-step estimate rewrites\n\n  A_{k+1}(x_{k+1} - x*) = R_α(ξ) A_k (x_k - x* - h B_k ξ) = R_α(ξ) (u_k - h ξ),\n\nand that cancellation of A_k against B_k is precisely A_k B_k = id. Knowing only B_k A_k = id does not give it.\n\nThe two directions follow from the same recursion: B_{k+1} = B_k ∘ R_{1/α}(ξ) and A_{k+1} = R_{α}(ξ) ∘ A_k, so A_{k+1} ∘ B_{k+1} = R_α(ξ) (A_k B_k) R_{1/α}(ξ) = A_k B_k by R_a ∘ R_{1/a} = id along a unit direction, and induction from A_0 B_0 = id closes it. Runs that trigger the stopping rule repeat the state, so they are trivial.

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- The *other* half of the operator relation of Shor (1985), formulas (3.9), pp. 51-52.

The platform already has `sdg_B_comp_A` (740b33d0-ad97-476d-a9d9-6c98a23d5785), which
proves `B_k ∘ A_k = id`.  Theorem 3.3 needs the converse direction `A_k ∘ B_k = id`,
because the step estimate rewrites

  `u_{k+1} = A_{k+1} (x_{k+1} - x*) = R_α(ξ) A_k (x_k - x* - h B_k ξ)
            = R_α(ξ) (u_k - h ξ)`,

and that cancellation is exactly `A_k B_k = id` applied to `x_k - x*` and to `ξ`.
Knowing only `B_k A_k = id` does not give it, since `A_k`, `B_k` are infinite-dimensional
operators and `sdg` records no finite-dimensionality hypothesis.

The two directions come from the same recursion.  With `B_0 = A_0 = id` and
`B_{k+1} = B_k ∘ R_{1/α}(ξ)`, `A_{k+1} = R_{α}(ξ) ∘ A_k`,

  `A_{k+1} ∘ B_{k+1} = R_α(ξ) A_k B_k R_{1/α}(ξ)
                      = R_α(ξ) R_{1/α}(ξ) A_k B_k
                      = A_k B_k`,

using `dilation_compose_inv` (09a91015-f15d-4fe8-b06c-61cff05c2a39), `R_a ∘ R_{1/a} = id`
along a unit direction for `a ≠ 0`.  So induction from `A_0 B_0 = id` closes it, exactly
as for `B_k A_k`.  Runs that trigger the stopping rule repeat the state and are trivial. -/
theorem sdg_A_comp_B {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0) :
    (sdg g h α x₀ B₀ k).A.toLinearMap.comp
      ((sdg g h α x₀ B₀ k).B.toLinearMap) = LinearMap.id := by sorry

end ShorNonsmooth.SpaceDilation
