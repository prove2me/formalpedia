-- Prove2me | Theorems.Thm_UnfairML_Coverage_eq_59
-- name    : UnfairML.Coverage.eq_59
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:28.980737+00:00
-- url     : https://prove2.me/theorems/b0efca87-77a8-4ea3-b1ac-48e68f232ed7
-- title:
--   Eqs. (55)–(59), p. 45 — the condition of Theorem 2 gives (βpγp/(σ²βpγp + (1 − σ²)(βpγr − αpγr)))^{1/2} ≤ 2 − σ
-- statement:
--   Under the standing assumptions and case (1), let $\sigma\in[\rho,1)$ with $\rho=1/(2-\gamma_p/\gamma_r)$. If
--   $$\frac{\alpha_p}{\beta_p}\le 1-\frac{1-(2-\sigma)^2\sigma^2}{(1-\sigma^2)(2-\sigma)^2}\cdot\frac{\gamma_p}{\gamma_r},$$
--   then
--   $$\left(\frac{\beta_p\gamma_p}{\sigma^2\beta_p\gamma_p+(1-\sigma^2)(\beta_p\gamma_r-\alpha_p\gamma_r)}\right)^{1/2}\le 2-\sigma .$$
--
--   Combined with (54), this makes $\phi^{ET}_p-\phi^{EO}_p$ non-negative.
--
--   **Formalization Note** The page prints the numerator of the condition as "1−(2−σ)²)σ²" with an unmatched parenthesis; it is read as $1-(2-\sigma)^2\sigma^2$, the form used in (56) (labelled correction).
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 45, proof of Theorem 2, eqs. (55)–(59)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Model

namespace UnfairML.Coverage

/-- Eqs. (55)–(59), p. 45: if `αp/βp ≤ 1 − [(1 − (2 − σ)²σ²)/((1 − σ²)(2 − σ)²)] · γp/γr`, then
`(βpγp/(σ²βpγp + (1 − σ²)(βpγr − αpγr)))^{1/2} ≤ 2 − σ`. -/
theorem eq_59 (P : Params) (hS : P.Standing) (hL : P.LowLoss) (σ : ℝ)
    (hσ : σ ∈ Set.Ico P.rho 1)
    (hcond : P.αp / P.βp ≤
      1 - (1 - (2 - σ) ^ 2 * σ ^ 2) / ((1 - σ ^ 2) * (2 - σ) ^ 2) * (P.γp / P.γr)) :
    Real.sqrt (P.βp * P.γp /
      (σ ^ 2 * P.βp * P.γp + (1 - σ ^ 2) * (P.βp * P.γr - P.αp * P.γr))) ≤ 2 - σ := by sorry
end UnfairML.Coverage
