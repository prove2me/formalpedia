-- Prove2me | Theorems.Thm_WassMMSE_FW_lemma_6_3_ii
-- name    : WassMMSE.FW.lemma_6_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:05.889573+00:00
-- url     : https://prove2.me/theorems/87c33f9c-3d8f-4079-b922-af73a68039b6
-- title:
--   Lemma 6.3 (ii), p. 24, corrected — g ≥ min_k ((1 − √(1 − δ))²α/(2δ))‖d‖²‖∇_[k]f(s)‖
-- statement:
--   In the setting of Section 6.1 (a product $\mathcal S=\times_k\mathcal S^{[k]}$ of convex compact sets, $f$ convex on $\mathcal S$ and differentiable at its points, an inexact oracle $F$ with precision $\delta\in(0,1]$), assume that the marginal feasible sets are $\alpha$-strongly convex with respect to $f$ (Assumption 6.1 (ii)). Let $s\in\mathcal S$ be a point at which every partial gradient $\nabla_{[k]}f(s)$ is nonzero, and let $d=F(s)-s$, $g=-d^\top\nabla f(s)$. Then
--
--   $$g\ \ge\ \min_{k\in\{1,\dots,K\}}\frac{\big(1-\sqrt{1-\delta}\big)^2\alpha}{2\delta}\,\|d\|^2\,\|\nabla_{[k]}f(s)\|.$$
--
--   Together with Lemma 6.3 (i), this lower bound on the gap in terms of the squared step length drives the linear rate in case (ii) of the proof of Theorem 6.2.
--
--   **Formalization Note** The paper prints the constant as $(1-\sqrt{1-\delta})\alpha/(2\delta)$, without the square. That is false for $\delta\in(0,1)$: the maximum over $\theta$ of $\delta\theta(1-\theta)/(1-\delta\theta)$ in (6.8), attained at $\theta^\star=(1-\sqrt{1-\delta})/\delta$ as the paper says, equals $(1-\sqrt{1-\delta})^2/\delta$, not $(1-\sqrt{1-\delta})/\delta$. Counterexample to the printed form: $K=1$, $\mathcal S$ the unit disk in $\mathbb R^2$ (1-strongly convex with respect to every $f$), $f(s)=s_2$, $s=(1,0)$, $\delta=3/4$ and $F(s)=(-\sqrt{1-\delta^2},-\delta)$, which satisfies (6.2) with equality; then $g=0.75$ while the printed bound is $\approx1.108$ (the corrected one is $\approx0.554$). At $\delta=1$ both constants equal $\alpha/2$. The case $\delta=0$ is excluded because the page divides by $\delta$. The minimum over $k$ is expressed through an arbitrary lower bound $m$ of all $\|\nabla_{[k]}f(s)\|$, and $\nabla_{[k]}f(s)\neq0$ is assumed so that the normalization in Assumption 6.1 (ii) is defined (it follows from Assumption 6.1 (iii)).
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 24, Lemma 6.3 (ii) (constant corrected; see Formalization Note)

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- Lemma 6.3 (ii), p. 24, **with the corrected constant**: under Assumption 6.1 (ii), for `δ ∈ (0, 1]`,
at `s ∈ 𝒮` with nonzero partial gradients and for every lower bound `m` of the `‖∇_{[k]}f(s)‖`
(in particular `m = min_k ‖∇_{[k]}f(s)‖`),
`g ≥ ((1 − √(1 − δ))² α/(2δ)) ‖d‖² m`. The page prints `(1 − √(1 − δ))` without the square, which
is false for `δ ∈ (0, 1)` (unit disk, `f(s) = s₂`, `s = (1, 0)`, `δ = 3/4`). -/
theorem lemma_6_3_ii
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {α : ℝ} (hα : IsStronglyConvexWrt S Sk f α) (hδ : 0 < δ) {s : BlockSpace K d} (hs : s ∈ S)
    (hgrad : ∀ k : Fin K, gradient f s k ≠ 0) :
    ∀ m : ℝ, (∀ k : Fin K, m ≤ ‖gradient f s k‖) →
      (1 - Real.sqrt (1 - δ)) ^ 2 * α / (2 * δ) * ‖fwDirection F s‖ ^ 2 * m ≤ fwGap f F s := by sorry

end WassMMSE.FW
