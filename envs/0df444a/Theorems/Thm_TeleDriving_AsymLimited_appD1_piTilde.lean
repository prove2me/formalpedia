-- Prove2me | Theorems.Thm_TeleDriving_AsymLimited_appD1_piTilde
-- name    : TeleDriving.AsymLimited.appD1_piTilde
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:34.644981+00:00
-- url     : https://prove2.me/theorems/66217802-ced7-40f1-8354-b810c7e850c9
-- title:
--   App. D.1, (19), p. 44 — π̃ < π_{m_λ,m_λ}(m_λ) and π̃ → (2a − 2)/(2a − 1)
-- statement:
--   Let $s > 0$, $\alpha \in (0,1)$, $a = 1/\alpha$, let the service rate be (4) and $m_\lambda = \lfloor\alpha\lambda s\rfloor$. Let $\pi_{m,n}(q)$ be the stationary distribution (2)–(3) and let
--   $$\tilde\pi_{m_\lambda,m_\lambda}(m_\lambda) = \frac{1}{1 + \sum_{i=0}^{m_\lambda-1}\frac{1}{\rho(m_\lambda)a^{i}}} \qquad (19).$$
--   Then:
--   1. for all sufficiently large $\lambda$, $\tilde\pi_{m_\lambda,m_\lambda}(m_\lambda) < \pi_{m_\lambda,m_\lambda}(m_\lambda)$;
--   2. $$\lim_{\lambda\to\infty}\tilde\pi_{m_\lambda,m_\lambda}(m_\lambda) = \frac{2a-2}{2a-1}.$$
--
--   Since $SL(m_\lambda,m_\lambda) = 1-\pi_{m_\lambda,m_\lambda}(m_\lambda)$, this gives an explicit asymptotic upper bound $1/(2a-1)$ for the service level of the system with as many drivers as vehicles.
--
--   **Formalization Note** The page states the strict inequality without qualification; it requires $m_\lambda \ge 2$ (at $m_\lambda = 1$ both sides coincide), so it is stated for all sufficiently large $\lambda$. The constant $a$ is written `1 / alpha`.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.1, (19), p. 44

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model
import Definitions.Def_TeleDriving_AsymLimited_Aux

namespace TeleDriving.AsymLimited

theorem appD1_piTilde (s alpha : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∀ᶠ lam in Filter.atTop,
      piTilde s alpha lam <
        TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam)) ∧
    Filter.Tendsto (piTilde s alpha) Filter.atTop
      (nhds ((2 * (1 / alpha) - 2) / (2 * (1 / alpha) - 1))) := by sorry

end TeleDriving.AsymLimited
