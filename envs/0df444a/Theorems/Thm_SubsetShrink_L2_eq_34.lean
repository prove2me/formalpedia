-- Prove2me | Theorems.Thm_SubsetShrink_L2_eq_34
-- name    : SubsetShrink.L2.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:30:45.211073+00:00
-- url     : https://prove2.me/theorems/977de1e3-c01d-43de-bc78-7721afd04fed
-- title:
--   (34), p. 39 — the inequality 2ab ≤ αa² + α⁻¹b²
-- statement:
--   For every $\alpha>0$ and all $a,b\in\mathbb R$,
--   $$2ab\le\alpha a^2+\alpha^{-1}b^2.$$
--
--   The proof of Theorem 2 applies this inequality with $\alpha=2$ and $\alpha=4$ to absorb the cross terms of (33) and of the fast-rate display into the left-hand side.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 39, proof of Theorem 2 (B.2), (34)

import Mathlib

namespace SubsetShrink.L2

/-- Proof of Theorem 2 (B.2), p. 39, (34): `2ab ≤ αa² + α⁻¹b²` for every `α > 0` and
`a, b ∈ ℝ`. -/
theorem eq_34 (α a b : ℝ) (hα : 0 < α) :
    2 * a * b ≤ α * a ^ 2 + α⁻¹ * b ^ 2 := by sorry

end SubsetShrink.L2
