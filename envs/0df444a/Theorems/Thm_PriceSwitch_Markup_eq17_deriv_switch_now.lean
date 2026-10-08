-- Prove2me | Theorems.Thm_PriceSwitch_Markup_eq17_deriv_switch_now
-- name    : PriceSwitch.Markup.eq17_deriv_switch_now
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:33.2518+00:00
-- url     : https://prove2.me/theorems/c005879f-ef86-4881-a439-21c722f7f3ab
-- title:
--   Eq. (17) — derivative of the immediate-switch revenue
-- statement:
--   For stock $n\ge1$, time-to-go $t>0$, initial price $a$ with rate $\lambda_a$, and second price $b$ with nonnegative rate $\lambda_b$, let $J(n,t;0)$ denote the revenue from switching immediately. Then
--
--   $$
--   \frac{\partial J(n,t;0)}{\partial t}=a\lambda_a-\lambda_a[J(n,t;0)-J(n-1,t;0)]-G(n,t),
--   $$
--
--   where $G(n,t)=a\lambda_a-b\lambda_b-b(\lambda_a-\lambda_b)\Pr\{N_b(t)\ge n\}$. This identity relates the fixed-switch revenue to the verification equation for the adaptive policy.
--
--   **Formalization Note** This calculus identity needs no stopping process or case ordering, so the statement omits those hypotheses. The count sum is represented by a Poisson random variable of mean $\lambda_bt$.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Appendix, proof of Theorem 1, Eq. (17), p. 1387; used in proof of Theorem 2, p. 1388, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markup

/-- Feng–Gallego (1995), Appendix, Eq. (17), p. 1387. -/
theorem eq17_deriv_switch_now
    (a la b lb : ℝ) (hlb : 0 ≤ lb) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => PriceSwitch.Markdown.switchRevenue a la b lb n u 0)
      (a * la - la * (PriceSwitch.Markdown.switchRevenue a la b lb n t 0 -
        PriceSwitch.Markdown.switchRevenue a la b lb (n - 1) t 0) - PriceSwitch.Markdown.G a la b lb n t) t := by sorry

end PriceSwitch.Markup
