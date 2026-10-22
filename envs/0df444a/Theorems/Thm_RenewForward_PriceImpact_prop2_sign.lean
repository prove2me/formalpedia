-- Prove2me | Theorems.Thm_RenewForward_PriceImpact_prop2_sign
-- name    : RenewForward.PriceImpact.prop2_sign
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:50.130449+00:00
-- url     : https://prove2.me/theorems/139ba492-570a-4d1b-861a-b0ee4554cdc3
-- title:
--   Proof of Proposition 2, p. 37 — if τ^N_ξ CV_ξ ≥ 27/(4N_R) then α4 ≥ 0, α2 > 0, α0 < 0, and s_ps is first negative, then positive
-- statement:
--   Let $\lambda > 0$, $N_R \ge 1$, and let $\mu_\theta, \sigma_\theta^2, \tau_\theta, \mu_\xi, \sigma_\xi^2, \tau_\xi$ be real numbers with $\mu_\xi > 0$, $\sigma_\xi^2 > 0$, $\sigma_\theta^2 \ge 0$ and
--   $$27\,\mu_\xi\sigma_\xi^2 \le 4N_R\,\tau_\xi.$$
--   Then $\alpha_4 \ge 0$, $\alpha_2 > 0$ and $\alpha_0 < 0$, and there is $\bar k^s_W > 0$ such that the quartic $s_{p_s}(k) = \alpha_0 + \alpha_1 k + \alpha_2 k^2 + \alpha_4 k^4$ satisfies
--   $$s_{p_s}(k) < 0 \text{ for } 0 \le k < \bar k^s_W, \qquad s_{p_s}(\bar k^s_W) = 0, \qquad s_{p_s}(k) > 0 \text{ for } k > \bar k^s_W.$$
--
--   Combined with the derivative formula, this is the single sign change of $\partial E[p_s]/\partial k_W$: the expected spot price first falls and then rises in wind capacity.
--
--   **Formalization Note.** For $\mu_\xi, \sigma_\xi > 0$ the hypothesis is equivalent to $\tau^N_\xi CV_\xi \ge \zeta := 27/(4N_R)$, with $CV_\xi = \sigma_\xi/\mu_\xi$ and $\tau^N_\xi = \tau_\xi/\sigma_\xi^3$. The page's proof writes ">" (giving $\alpha_4 > 0$); the proposition's "≥" is used here, where $\alpha_4 = 0$ is allowed and $\alpha_2 > 0$ still gives the conclusion. The page states $\alpha_0 \le 0$; for $\mu_\xi > 0$ it is strict. No hypothesis is placed on $a, c, p_R, \mu_\theta, \tau_\theta$, which enter only $\alpha_1$.
-- source:
--   Peura & Bunn, Renewable power and electricity prices: The impact of forward markets, author-accepted manuscript, LBS Research Online eprint 1432 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3710), p. 37, proof of Proposition 2

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting
import Definitions.Def_RenewForward_PriceImpact_ClosedForms

namespace RenewForward.PriceImpact

/-- Proof of Proposition 2, p. 37: under `4 N_R τ_ξ ≥ 27 µ_ξ σ²_ξ` (equivalently `τ^N_ξ CV_ξ ≥ 27/(4N_R)`),
`α4 ≥ 0`, `α2 > 0`, `α0 < 0`, and `s_ps` is negative on `[0, k̄^s_W)`, zero at `k̄^s_W > 0`, positive after. -/
theorem prop2_sign (M : Params) (m : Moments) (hlam : 0 < M.lam) (hNR : 1 ≤ M.NR)
    (hmu : 0 < m.muX) (hs2X : 0 < m.s2X) (hs2T : 0 ≤ m.s2T)
    (hζ : 27 * m.muX * m.s2X ≤ 4 * (M.NR : ℝ) * m.tauX) :
    0 ≤ alpha4 M m ∧ 0 < alpha2 M m ∧ alpha0 M m < 0 ∧
    ∃ ks : ℝ, 0 < ks ∧ spsPoly M m ks = 0 ∧
      (∀ k ∈ Set.Ico 0 ks, spsPoly M m k < 0) ∧ (∀ k : ℝ, ks < k → 0 < spsPoly M m k) := by sorry

end RenewForward.PriceImpact
