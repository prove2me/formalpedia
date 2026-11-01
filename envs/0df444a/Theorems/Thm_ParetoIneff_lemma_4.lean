-- Prove2me | Theorems.Thm_ParetoIneff_lemma_4
-- name    : ParetoIneff.lemma_4
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:23:58.836983+00:00
-- url     : https://prove2.me/theorems/008070f8-740d-442a-bd2f-95b351011e32
-- title:
--   Lemma 4 — a ratio bound for two load terms
-- statement:
--   For all reals $x,y\ge0$ and $\beta,\gamma>0$,
--   $$
--   x+\beta y\le\Bigl(\frac{\beta}{\gamma}+1\Bigr)\max\{x,\gamma y\}.
--   $$
--   This is the last step in the proofs of Theorems 7 and 8.
--
--   Differences from the source:
--   - generalization: $\dfrac{x+\beta y}{\max\{x,\gamma y\}}\le\dfrac{\beta}{\gamma}+1$ for $x,y\ge0$ with $xy\ne0$ → the cross-multiplied inequality for all $x,y\ge0$; reason: Theorems 7 and 8 apply the lemma with $x=0$ or $y=0$; dividing by $\max\{x,\gamma y\}>0$ gives the printed form
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Lemma 4, Appendix A, p.25

import Mathlib

namespace ParetoIneff

/-- **Lemma 4**, Appendix A, arXiv:1809.03454v7, p.25: for any nonnegative reals `x, y` and all
positive reals `β, γ`,
`x + βy ≤ (β/γ + 1) · max{x, γy}`.

**Formalization Note** The paper states the ratio form `(x + βy) / max{x, γy} ≤ β/γ + 1` under
`xy ≠ 0`. The cross-multiplied form holds for all `x, y ≥ 0` (including `x = 0` or `y = 0`, the
cases in which the proofs of Theorems 7 and 8 apply it) and gives the printed form by dividing by
`max{x, γy} > 0`. -/
theorem lemma_4 (x y β γ : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hβ : 0 < β) (hγ : 0 < γ) :
    x + β * y ≤ (β / γ + 1) * max x (γ * y) := by sorry

end ParetoIneff
