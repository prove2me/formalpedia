-- Prove2me | Theorems.Thm_RevenueOrdered_Nesting_minLStar_antitone
-- name    : RevenueOrdered.Nesting.minLStar_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:10.794575+00:00
-- url     : https://prove2.me/theorems/29fc27bb-4b13-4d06-9ce3-52eb35ea9e1b
-- title:
--   Lemma .1 — min 𝓛∗(δ₂) ⩽ min 𝓛∗(δ₁) for δ₁ ⩽ δ₂ and δ₁ + r_k ⩾ 0
-- statement:
--   Let $\mathcal P$ be a regular discrete choice model on a finite nonempty set of products $\mathcal C$, and $r:\mathcal C\to\mathbb R_{>0}$ a revenue function with distinct values $r_1<\cdots<r_k$. For $\delta\in\mathbb R$ let $\mathcal L^*(\delta)\subseteq[k]$ be the set of indices $\ell$ whose revenue-ordered assortment $S_\ell=\{x : r(x)\ge r_\ell\}$ maximises $\sum_{x\in S_\ell}\mathcal P(x,S_\ell)(r(x)+\delta)$ over $\ell\in[k]$.
--
--   If $\delta_1,\delta_2\in\mathbb R$ satisfy $\delta_1+r_k\ge 0$ and $\delta_1\le\delta_2$, then
--   $$
--   \min\mathcal L^*(\delta_2)\le\min\mathcal L^*(\delta_1).
--   $$
--
--   In words: raising every revenue by a larger amount can only enlarge (weakly) the largest optimal revenue-ordered assortment. This is the single-period comparison that, applied with $\delta=-\Delta\mathcal J$, yields both monotonicity statements of Theorem 5.1.
--
--   **Formalization Note** The hypothesis $\delta_1+r_k\ge 0$ is kept as in the paper's statement, where it is the condition under which $\mathcal L^*$ is introduced.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 35, Appendix B, Lemma .1

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_LStar

namespace RevenueOrdered.Nesting

/-- Lemma .1 (Berbeglia–Joret, arXiv:1606.01371v3, App. B, p. 35): for `δ₁ + r_k ≥ 0` and
`δ₁ ≤ δ₂`, `min 𝓛∗(δ₂) ≤ min 𝓛∗(δ₁)`. -/
theorem minLStar_antitone {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : IsRegular P) (hr : ∀ x, 0 < r x)
    {δ₁ δ₂ : ℝ} (hδ₁ : δ₁ + topRevenue r ≥ 0) (hδ : δ₁ ≤ δ₂) :
    minLStar P r δ₂ ≤ minLStar P r δ₁ := by sorry

end RevenueOrdered.Nesting
