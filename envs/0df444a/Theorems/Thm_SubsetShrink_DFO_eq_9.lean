-- Prove2me | Theorems.Thm_SubsetShrink_DFO_eq_9
-- name    : SubsetShrink.DFO.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:21.637543+00:00
-- url     : https://prove2.me/theorems/db39d1cd-0acc-44d4-b3d3-330856379409
-- title:
--   (9), p. 8 — an L₀-smooth f lies below its quadratic model Q_L(β; α) for every L ≥ L₀
-- statement:
--   Let $f:\mathbb R^p\to\mathbb R$ be a differentiable convex function whose gradient is $L_0$-Lipschitz, with $L_0\ge0$:
--   $$\|\nabla f(\beta)-\nabla f(\alpha)\|_2\le L_0\|\beta-\alpha\|_2\qquad\forall\,\beta,\alpha\in\mathbb R^p .$$
--   Then for every $L\ge L_0$ and all $\alpha,\beta\in\mathbb R^p$,
--   $$f(\beta)\le f(\alpha)+\langle\nabla f(\alpha),\beta-\alpha\rangle+\frac L2\|\beta-\alpha\|_2^2=Q_L(\beta;\alpha).$$
--
--   This is the quadratic upper bound (the "descent lemma") that the DFO method minimizes in place of $f$ at each step; it is the first ingredient of the proof of Proposition 2.
--
--   **Formalization Note** Convexity is part of the setting of (7)–(8) ("an $L_0$-smooth convex function") and is kept as a hypothesis as printed. The gradient is Mathlib's `gradient f`.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 8, (8)–(9)

import Mathlib
import Definitions.Def_SubsetShrink_DFO_Model

namespace SubsetShrink.DFO

/-- (9), p. 8 (Mazumder, Radchenko & Dedieu, arXiv:1708.03288v4): if `f : ℝᵖ → ℝ` is a
differentiable convex function whose gradient is `L₀`-Lipschitz ((8)), then for every
`L ≥ L₀` and all `α, β ∈ ℝᵖ`,
`f(β) ≤ f(α) + ⟨∇f(α), β − α⟩ + (L/2)‖β − α‖₂² = Q_L(β; α)`. -/
theorem eq_9 {p : ℕ} (f : E p → ℝ) (L0 L : ℝ)
    (hdiff : Differentiable ℝ f) (hconv : ConvexOn ℝ Set.univ f) (hL0nn : 0 ≤ L0)
    (hL0 : ∀ β α : E p, ‖gradient f β - gradient f α‖ ≤ L0 * ‖β - α‖)
    (hL : L0 ≤ L) :
    ∀ β α : E p, f β ≤ QL f L β α := by sorry

end SubsetShrink.DFO
