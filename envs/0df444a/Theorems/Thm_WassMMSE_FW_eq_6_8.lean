-- Prove2me | Theorems.Thm_WassMMSE_FW_eq_6_8
-- name    : WassMMSE.FW.eq_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:20.432568+00:00
-- url     : https://prove2.me/theorems/1e31f9d9-8965-4818-9ea0-b6db9fd8009a
-- title:
--   (6.8), p. 24 — g ≥ min_k (α/2)‖F(s) − s‖²‖∇_[k]f(s)‖ · δθ(1 − θ)/(1 − δθ)
-- statement:
--   In the setting of Section 6.1 (a product $\mathcal S=\times_k\mathcal S^{[k]}$ of convex compact sets, $f$ convex on $\mathcal S$ and differentiable at its points, an inexact oracle $F$ with precision $\delta\in[0,1]$), assume that the marginal feasible sets are $\alpha$-strongly convex with respect to $f$ (Assumption 6.1 (ii)). Let $s\in\mathcal S$ be a point at which every partial gradient $\nabla_{[k]}f(s)$ is nonzero, and let $g=-(F(s)-s)^\top\nabla f(s)$. Then for every $\theta\in[0,1]$ with $\delta\theta<1$,
--
--   $$g\ \ge\ \min_{k\in\{1,\dots,K\}}\frac{\alpha}{2}\|F(s)-s\|^2\,\|\nabla_{[k]}f(s)\|\;\frac{\delta\theta(1-\theta)}{1-\delta\theta}.$$
--
--   This is the intermediate bound from which Lemma 6.3 (ii) follows by optimizing over $\theta$.
--
--   **Formalization Note** The minimum over $k$ is expressed through an arbitrary lower bound $m$ of all $\|\nabla_{[k]}f(s)\|$ (equivalent, since the factor in front is nonnegative; taking $m=\min_k\|\nabla_{[k]}f(s)\|$ recovers the display). Two hypotheses are added where the page divides: $\delta\theta<1$ (at $\delta=\theta=1$ the factor $1/(1-\delta\theta)$ is undefined) and $\nabla_{[k]}f(s)\neq0$ for all $k$ (the normalization in Assumption 6.1 (ii) is undefined otherwise; it follows from Assumption 6.1 (iii)).
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 24, (6.8), proof of Lemma 6.3

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- (6.8), proof of Lemma 6.3, p. 24: under Assumption 6.1 (ii), at `s ∈ 𝒮` with nonzero partial
gradients, for every `θ ∈ [0, 1]` with `δθ < 1` and every lower bound `m` of the
`‖∇_{[k]}f(s)‖` (so in particular `m = min_k ‖∇_{[k]}f(s)‖`),
`g ≥ (α/2)‖F(s) − s‖² m · δθ(1 − θ)/(1 − δθ)`. -/
theorem eq_6_8
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {α : ℝ} (hα : IsStronglyConvexWrt S Sk f α) {s : BlockSpace K d} (hs : s ∈ S)
    (hgrad : ∀ k : Fin K, gradient f s k ≠ 0) :
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, δ * θ < 1 → ∀ m : ℝ, (∀ k : Fin K, m ≤ ‖gradient f s k‖) →
      α / 2 * ‖F s - s‖ ^ 2 * m * (δ * θ * (1 - θ) / (1 - δ * θ)) ≤ fwGap f F s := by sorry

end WassMMSE.FW
