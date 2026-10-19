-- Prove2me | Theorems.Thm_RenewForward_PriceImpact_prop2_forward
-- name    : RenewForward.PriceImpact.prop2_forward
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:43.817471+00:00
-- url     : https://prove2.me/theorems/91c39e40-b5d5-432a-928e-99cdc738d5eb
-- title:
--   Proof of Proposition 2, p. 37 — the closed-form forward price a_f − 2b_fω/ν has eventually positive derivative in k_W
-- statement:
--   Let $\lambda > 0$, $N_R \ge 1$, and let $\mu_\theta, \sigma_\theta^2, \tau_\theta, \mu_\xi, \sigma_\xi^2, \tau_\xi$ be real numbers with $\sigma_\xi^2 > 0$, $\sigma_\theta^2 \ge 0$ and $2\mu_\xi\sigma_\xi^2 + \tau_\xi > 0$. Let $p_f(k_W) = a_f - 2b_f\omega/\nu$ be the closed-form equilibrium forward price of Theorem 1. Then there is $\bar k^f_W$ such that
--   $$\frac{d p_f}{d k_W}(k_W) > 0 \qquad\text{for all } k_W \ge \bar k^f_W.$$
--
--   On the page, $\partial p_f/\partial k_W = s_{p_f}(k_W)/\nu^2$ for a polynomial $s_{p_f}$ whose highest-order term is strictly positive; this statement is that eventual sign. With Theorem 1 it gives the forward-price part of Proposition 2.
--
--   **Formalization Note.** The page says the leading term is positive "for $\sigma_\xi > 0$ (which is implied by the condition on $s_{p_s}$)". The leading coefficient is a positive multiple of $\sigma_\xi^4(2\mu_\xi\sigma_\xi^2 + \tau_\xi)$, so the hypothesis $2\mu_\xi\sigma_\xi^2 + \tau_\xi > 0$ is stated; it follows from the condition $27\mu_\xi\sigma_\xi^2 \le 4N_R\tau_\xi$ with $\mu_\xi, \sigma_\xi^2 > 0$, and also equals $\mathrm{Cov}(\xi, \xi^2) > 0$ for a non-degenerate $\xi \ge 0$.
-- source:
--   Peura & Bunn, Renewable power and electricity prices: The impact of forward markets, author-accepted manuscript, LBS Research Online eprint 1432 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3710), p. 37, proof of Proposition 2 (forward price)

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting
import Definitions.Def_RenewForward_PriceImpact_ClosedForms

namespace RenewForward.PriceImpact

/-- Proof of Proposition 2, p. 37: the derivative of the closed-form forward price `a_f − 2 b_f ω/ν` in
`k_W` is eventually strictly positive. -/
theorem prop2_forward (M : Params) (m : Moments) (hlam : 0 < M.lam) (hNR : 1 ≤ M.NR)
    (hs2X : 0 < m.s2X) (hs2T : 0 ≤ m.s2T) (hpos : 0 < 2 * m.muX * m.s2X + m.tauX) :
    ∃ kf : ℝ, ∀ kW : ℝ, kf ≤ kW → 0 < deriv (fwdPriceClosed M m) kW := by sorry

end RenewForward.PriceImpact
