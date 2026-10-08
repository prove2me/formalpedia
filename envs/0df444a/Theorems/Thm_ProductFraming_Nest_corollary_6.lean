-- Prove2me | Theorems.Thm_ProductFraming_Nest_corollary_6
-- name    : ProductFraming.Nest.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:21.053985+00:00
-- url     : https://prove2.me/theorems/00949f68-76f4-488f-993a-c88fb1da1f07
-- title:
--   Corollary 6 — $\mathbb E[X/\mathbb E[\min(X,Y)\mid X]] \le \mathbb E[W/\mathbb E[\min(Z,W)\mid W]]$
-- statement:
--   Let $X\in[m]$ have law $\lambda$ satisfying Assumption A3 (NBUE), let $Y$ be independent of $X$ with the same law, and let $W,Z$ be independent exponential random variables with mean $\mathbb E[W]=\mathbb E[Z]=\mathbb E[X]=\mu$. Then
--   $$\mathbb E\Big[\frac{X}{\mathbb E[\min(X,Y)\mid X]}\Big]=\sum_{x\in[m]}\lambda(x)\,\frac{x}{\mathbb E[\min(X,x)]}\ \le\ \mathbb E\Big[\frac{W}{\mathbb E[\min(Z,W)\mid W]}\Big]=\int\frac{w}{\int\min(z,w)\,dF_Z(z)}\,dF_W(w).$$
--
--   Together with Proposition 3, it bounds $1/\gamma$ by an explicit exponential integral.
--
--   **Formalization Note** Independence is encoded by writing the conditional expectations as iterated integrals: $\mathbb E[\min(X,Y)\mid X=x]=\mathbb E[\min(X,x)]$ and $\mathbb E[\min(Z,W)\mid W=w]=\int\min(z,w)\,dF_Z(z)$. The laws of $W$ and $Z$ are `expMeasure` with rate $1/\mu$. At $w=0$ the integrand is $0/0=0$ in Lean, on a null set.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.2, p. 37, Corollary 6

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

namespace ProductFraming.Nest

open Finset MeasureTheory ProbabilityTheory

/-- Corollary 6 (Gallego, Li, Truong, Wang 2020, p. 37): with `Y` i.i.d. as the NBUE `X` and `W`,
`Z` independent exponential with mean `E[X]`,
`E[X / E[min(X, Y) | X]] ≤ E[W / E[min(Z, W) | W]]`. Independence is encoded by the iterated
integral. -/
theorem corollary_6 (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam) :
    ∑ x ∈ Icc 1 m, lam x * (x : ℝ) / Emin m lam (x : ℝ) ≤
      ∫ w, w / (∫ z, min z w ∂(expMeasure (mean m lam)⁻¹)) ∂(expMeasure (mean m lam)⁻¹) := by sorry

end ProductFraming.Nest
