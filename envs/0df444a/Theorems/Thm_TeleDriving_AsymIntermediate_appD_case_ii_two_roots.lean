-- Prove2me | Theorems.Thm_TeleDriving_AsymIntermediate_appD_case_ii_two_roots
-- name    : TeleDriving.AsymIntermediate.appD_case_ii_two_roots
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:48.530394+00:00
-- url     : https://prove2.me/theorems/0f377757-5ab3-4ea5-b2bc-e7a609bf90ef
-- title:
--   App. D, case (ii), p. 42 — for the rate (4) in the intermediate range, ρ(q) = 1 has two roots q₁ < q₂ in [λs, m] and ρ < 1 exactly between them
-- statement:
--   Let $s > 0$ and $\lambda > 0$ with $\lambda s \ge 2$, and let $m$ be a number of vehicles with
--   $$\lambda s + 3\left(\frac{\lambda s}{2}\right)^{2/3} - 1 < m < 2\lambda s .$$
--   Take the service rate (4), $\mu(m,q) = [s/\sqrt{m-q+1} + s]^{-1}$, so that by (13)
--   $$\rho(q) = \frac{\lambda}{q}\left(\frac{s}{\sqrt{m-q+1}} + s\right).$$
--   Then there are $q_1 < q_2$ in $[\lambda s, m]$ with $\rho(q_1) = \rho(q_2) = 1$ such that, for every $q \in (0, m]$,
--   $$\rho(q) < 1 \iff q_1 < q < q_2 ,$$
--   and $\rho(q) \ge 1$ for all other $q \in (0,m]$.
--
--   The interval of $m$ is the intermediate regime $\gamma_1(\lambda) < m < \gamma_2(\lambda)$ for this rate, with $\gamma_1(\lambda) = \lambda s + 3(\lambda s/2)^{2/3} - 1$ and $\gamma_2(\lambda) = 2\lambda s$ (equation (14)); the two roots are the points $q_1$ and $q_2$ that locate the two modes of the stationary distribution, used in the proof of Theorem 2.B.
--
--   **Formalization Note** The hypothesis $\lambda s \ge 2$ is not on the page. The paper's argument places the maximizer $q_{\max} = m + 1 - (\lambda s/2)^{2/3}$ of its auxiliary function inside $[\lambda s, m]$, which requires $\lambda s \ge 2$; without it the statement fails (e.g. $s = 1$, $\lambda = 0.6$, $m = 1$ satisfies the range but $\rho \ge 1$ on all of $(0,1]$). The hypothesis holds for all large $\lambda$, which is the only use the paper makes of the claim. The roots are stated as existing numbers with the characterizing property; $q \le 0$ is excluded because $\rho$ divides by $q$.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D, p. 42, (13), case (ii) and (14)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymIntermediate

theorem appD_case_ii_two_roots (s lam : ℝ) (hs : 0 < s) (hls : 2 ≤ lam * s) (m : ℕ)
    (hm1 : lam * s + 3 * (lam * s / 2) ^ ((2 : ℝ) / 3) - 1 < (m : ℝ))
    (hm2 : (m : ℝ) < 2 * lam * s) :
    ∃ q1 q2 : ℝ, lam * s ≤ q1 ∧ q1 < q2 ∧ q2 ≤ (m : ℝ) ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam m q1 = 1 ∧ TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam m q2 = 1 ∧
      ∀ q ∈ Set.Ioc (0 : ℝ) m, (TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam m q < 1 ↔ q1 < q ∧ q < q2) := by sorry

end TeleDriving.AsymIntermediate
