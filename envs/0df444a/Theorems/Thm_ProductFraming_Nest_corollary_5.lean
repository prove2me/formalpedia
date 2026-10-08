-- Prove2me | Theorems.Thm_ProductFraming_Nest_corollary_5
-- name    : ProductFraming.Nest.corollary_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:12:06.783875+00:00
-- url     : https://prove2.me/theorems/54b940e3-f93a-4ade-98ec-1de72f2644b6
-- title:
--   Corollary 5 — $\mathbb E[\min(X,x)] \ge \mathbb E[\min(Z,x)]$ for $x \ge 0$
-- statement:
--   Let $X\in[m]$ have law $\lambda$ satisfying Assumption A3 (NBUE), and let $Z$ be exponential with mean $\mathbb E[Z]=\mathbb E[X]=\mu$. Then for all real $x\ge0$,
--   $$\mathbb E[\min(X,x)]=\sum_{y\in[m]}\lambda(y)\min(y,x)\ \ge\ \mathbb E[\min(Z,x)].$$
--
--   It bounds the denominators of the objective of (6) from below by their exponential counterparts.
--
--   **Formalization Note** The page prints the conclusion as "$\mathbb E[\min(X,x)]\ge\mathbb E[\min(X,x)]$", a typo: the proof ends with $\mathbb E[\min(Z,x)]$ on the right, which is what is formalized. The law of $Z$ is `expMeasure` with rate $1/\mu$.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.2, p. 37, Corollary 5 (typo in the printed right-hand side corrected)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

namespace ProductFraming.Nest

open Finset MeasureTheory ProbabilityTheory

/-- Corollary 5 (Gallego, Li, Truong, Wang 2020, p. 37), with the page's typo corrected: if `X` is
NBUE and `Z` is exponential with `E[Z] = E[X]`, then `E[min(X, x)] ≥ E[min(Z, x)]` for all
`x ≥ 0`. -/
theorem corollary_5 (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam) :
    ∀ x : ℝ, 0 ≤ x → ∫ z, min z x ∂(expMeasure (mean m lam)⁻¹) ≤ Emin m lam x := by sorry

end ProductFraming.Nest
