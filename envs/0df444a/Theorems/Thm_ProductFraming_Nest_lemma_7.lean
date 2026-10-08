-- Prove2me | Theorems.Thm_ProductFraming_Nest_lemma_7
-- name    : ProductFraming.Nest.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:01.757397+00:00
-- url     : https://prove2.me/theorems/8f846944-fc72-464d-8ecd-d0d883aa2767
-- title:
--   Lemma 7 — an NBUE page count is dominated by the exponential in the increasing convex order
-- statement:
--   Let $X\in[m]$ have law $\lambda$ satisfying Assumption A3 (NBUE), and let $Z$ be an exponential random variable with mean $\mathbb E[Z]=\mathbb E[X]=\mu$. Then for every function $g$ that is increasing and convex on $[0,\infty)$ and integrable under the law of $Z$,
--   $$\mathbb E[g(X)]=\sum_{x\in[m]}\lambda(x)\,g(x)\ \le\ \mathbb E[g(Z)]=\int_0^\infty g(z)\,\frac1\mu e^{-z/\mu}\,dz.$$
--
--   This comparison with the exponential distribution is what produces the constant $\pi^2/6$ in the analysis of NEST.
--
--   **Formalization Note** The law of $Z$ is Mathlib's `expMeasure`, whose parameter is the rate $1/\mu$. Integrability of $g$ under that law is added: Lean's Bochner integral is $0$ for a non-integrable function, while on the page $\mathbb E[g(Z)]=+\infty$ makes the claim trivial in that case. Increasing and convex are required on $[0,\infty)$, where both laws live; increasing means nondecreasing.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, A.2, p. 36, Lemma 7

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

namespace ProductFraming.Nest

open Finset MeasureTheory ProbabilityTheory

/-- Lemma 7 (Gallego, Li, Truong, Wang 2020, p. 36): if `X` is NBUE and `Z` is exponential with
`E[Z] = E[X]`, then `E[g(X)] ≤ E[g(Z)]` for every increasing convex `g`. Mathlib's
`expMeasure` takes the rate, so the law of `Z` is `expMeasure (E[X])⁻¹`. The integrability of
`g` under the law of `Z` is added (otherwise the Bochner integral is `0`). -/
theorem lemma_7 (m : ℕ) (hm : 1 ≤ m) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) (hA3 : IsNBUE m lam)
    (g : ℝ → ℝ) (hg_mono : MonotoneOn g (Set.Ici 0)) (hg_conv : ConvexOn ℝ (Set.Ici 0) g)
    (hg_int : Integrable g (expMeasure (mean m lam)⁻¹)) :
    ∑ x ∈ Icc 1 m, lam x * g (x : ℝ) ≤ ∫ z, g z ∂(expMeasure (mean m lam)⁻¹) := by sorry

end ProductFraming.Nest
