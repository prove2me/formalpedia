-- Prove2me | Theorems.Thm_PriceSwitch_UpOrDown_eq16_deriv_switch_now
-- name    : PriceSwitch.UpOrDown.eq16_deriv_switch_now
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:04:17.221548+00:00
-- url     : https://prove2.me/theorems/992875a1-385d-4472-9622-9b4490151a91
-- title:
--   §5, Eq. (16), p. 1385 — derivative in t of the switch-at-once revenue J^i(n,t;0)
-- statement:
--   Let $a, \lambda_a, b$ be real numbers and $\lambda_b \ge 0$. Let $J(n,t;0)$ be the expected revenue of switching at once from price $a$ to price $b$ (so that $J(n,t;0) = b\,E\min(n, N_b(t))$ with $N_b(t)$ Poisson of mean $\lambda_b t$), and let $G(n,t) = a\lambda_a - b\lambda_b - b(\lambda_a - \lambda_b)P(N_b(t) \ge n)$. Then for every $n \ge 1$ and every $t > 0$, $J(n,\cdot;0)$ is differentiable at $t$ and
--
--   $$
--   \frac{\partial J(n,t;0)}{\partial t} = a\lambda_a - \lambda_a\bigl[J(n,t;0) - J(n-1,t;0)\bigr] - G(n,t).
--   $$
--
--   In §5 this is applied with $(a,\lambda_a,b,\lambda_b) = (p,\lambda,p_i,\lambda_i)$, giving (16): $\partial J^i(n,t;0)/\partial t = r - \lambda[J^i(n,t;0) - J^i(n-1,t;0)] - G^i(n,t)$ for $i = 1,2$. The identity converts the verification conditions of Lemma 1 into conditions on the excess $F = V - J^i(\cdot;0)$, which is how the proof of Theorem 3 begins.
--
--   **Formalization Note** The identity is a calculus fact about Poisson tails and is stated for arbitrary real $a, \lambda_a, b$; only $\lambda_b \ge 0$ is needed, so that the Poisson mean $\lambda_b t$ is nonnegative. It is the same statement as (17) of the Appendix (p. 1387), stated in the generic pair $(a,b)$.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), §5, Eq. (16), p. 1385 (from Eq. (17), Appendix, p. 1387)

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

/-- Feng–Gallego (1995), §5, Eq. (16), p. 1385 (the instance `(a, la, b, lb) = (p, λ, p_i, λ_i)` of (17),
p. 1387). -/
theorem eq16_deriv_switch_now
    (a la b lb : ℝ) (hlb : 0 ≤ lb) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => PriceSwitch.Markdown.switchRevenue a la b lb n u 0)
      (a * la - la * (PriceSwitch.Markdown.switchRevenue a la b lb n t 0 -
        PriceSwitch.Markdown.switchRevenue a la b lb (n - 1) t 0) - PriceSwitch.Markdown.G a la b lb n t) t := by sorry

end PriceSwitch.UpOrDown
