-- Prove2me | Theorems.Thm_TeleDriving_AsymLimited_appD1_rho_gt
-- name    : TeleDriving.AsymLimited.appD1_rho_gt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:45.823489+00:00
-- url     : https://prove2.me/theorems/8ccc9dd9-a3cf-4974-9883-cb0765613e22
-- title:
--   App. D.1, p. 44 — with m_λ = ⌊αλs⌋, ρ(k) > 1/α for 1 ≤ k ≤ m_λ
-- statement:
--   Let $s > 0$ be the expected trip time, $\alpha \in (0,1)$, and let the service rate be (4), $\mu(m,q) = [s/\sqrt{m-q+1}+s]^{-1}$, so that the load is $\rho(q) = \frac{\lambda}{q}\big(\frac{s}{\sqrt{m-q+1}}+s\big)$ (display (13)). For every arrival rate $\lambda > 0$, with $m_\lambda = \lfloor \alpha\lambda s\rfloor$ vehicles,
--   $$\rho(k) > \frac{1}{\alpha} \qquad \text{for every integer } 1 \le k \le m_\lambda.$$
--
--   In the supply-limited regime $\alpha < 1$, the load exceeds $a = 1/\alpha > 1$ uniformly over all occupancy levels; this geometric lower bound drives the comparison probability (19) and the vanishing of the low-occupancy mass in the proof of Theorem 2.A.
--
--   **Formalization Note** The statement holds for every $\lambda > 0$, not only eventually. When $m_\lambda = 0$ the range of $k$ is empty.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.1, p. 44 (using (13), p. 42)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymLimited

theorem appD1_rho_gt (s alpha : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∀ lam : ℝ, 0 < lam → ∀ k : ℕ, k ∈ Finset.Icc 1 (TeleDriving.ScarceFleet.mLam alpha s lam) →
      1 / alpha < TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (k : ℝ) := by sorry

end TeleDriving.AsymLimited
