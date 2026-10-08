-- Prove2me | Theorems.Thm_PriceSwitch_Markdown_eq17_deriv_switch_now
-- name    : PriceSwitch.Markdown.eq17_deriv_switch_now
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:08:03.830203+00:00
-- url     : https://prove2.me/theorems/0175bea2-e9b2-42e2-b967-8312663da7f5
-- title:
--   Eq. (17) — derivative of the immediate-switch revenue
-- statement:
--   Let $a$ and $b$ be prices, let $\lambda_a$ be any real parameter and let $\lambda_b\ge0$ be the second Poisson rate. For an inventory $n\ge1$ and time-to-go $t>0$, the expected revenue $J(n,t;0)$ from switching immediately satisfies
--
--   $$
--   \frac{\partial J(n,t;0)}{\partial t}=a\lambda_a-\lambda_a[J(n,t;0)-J(n-1,t;0)]-G(n,t).
--   $$
--
--   This identity relates the immediate-switch revenue to the differential conditions of the paper's verification lemma.
--
--   **Formalization Note** This is a deterministic calculus identity for the Poisson-tail definition of $J$, so it needs no stochastic process, probability space, or markdown ordering. The sum of independent Poisson counts in $J$ is represented by their combined Poisson law. The parameter $\lambda_a$ cancels algebraically; $\lambda_b\ge0$ ensures that the Poisson mean is meaningful.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Appendix, proof of Theorem 1, Eq. (17), p. 1387, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markdown

/-- Feng–Gallego (1995), Appendix, Eq. (17), p. 1387. -/
theorem eq17_deriv_switch_now
    (a la b lb : ℝ) (hlb : 0 ≤ lb) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => switchRevenue a la b lb n u 0)
      (a * la - la * (switchRevenue a la b lb n t 0 -
        switchRevenue a la b lb (n - 1) t 0) - G a la b lb n t) t := by sorry

end PriceSwitch.Markdown
