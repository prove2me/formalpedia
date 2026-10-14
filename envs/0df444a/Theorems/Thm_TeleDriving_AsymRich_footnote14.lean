-- Prove2me | Theorems.Thm_TeleDriving_AsymRich_footnote14
-- name    : TeleDriving.AsymRich.footnote14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:58.901474+00:00
-- url     : https://prove2.me/theorems/81f0d433-e0f3-46bb-9a7b-065c41e03421
-- title:
--   Footnote 14, pp. 22–23 — SL(m_λ, m_λ) − SL(m_λ, ⌊(1+δ)q₃⌋) → 0 when α > 2
-- statement:
--   Let $s > 0$, $\alpha > 2$, $m_\lambda = \lfloor\alpha\lambda s\rfloor$, and let the service rate be (4). Let $q_3(\lambda)$ be, for all sufficiently large $\lambda$, a root of $\rho = 1$ in $[\lambda s, m_\lambda]$ (as in case (iii) of Appendix D). For every $\delta$ with $0 < \delta < \alpha - 1$,
--
--   $$\lim_{\lambda\to\infty} \Big[ SL(m_\lambda, m_\lambda) - SL\big(m_\lambda, \lfloor (1+\delta) q_3 \rfloor\big) \Big] = 0.$$
--
--   A fleet of $m_\lambda$ vehicles operated by only $\lfloor (1+\delta) q_3\rfloor \approx (1+\delta)\lambda s$ remote drivers asymptotically loses no service level compared with one driver per vehicle. The paper uses this to explain why the bound of Theorem 2.C does not depend on the tolerance $\epsilon$.
--
--   **Formalization Note** The footnote says "for any $\delta > 0$". It is read as $0 < \delta < \alpha - 1$: for larger $\delta$ the number of drivers $\lfloor(1+\delta)q_3\rfloor$ exceeds $m_\lambda$ for large $\lambda$, where $SL(m,n)$ is not defined by the paper. $q_3$ is characterized by an eventually-holding hypothesis rather than by the closed form (17).
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), footnote 14, pp. 22–23

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymRich

theorem footnote14 (s alpha : ℝ) (hs : 0 < s) (ha : 2 < alpha) (q3 : ℝ → ℝ)
    (hq3 : ∀ᶠ lam in Filter.atTop, lam * s ≤ q3 lam ∧ q3 lam ≤ (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ∧
      TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (q3 lam) = 1)
    (delta : ℝ) (hd0 : 0 < delta) (hd1 : delta < alpha - 1) :
    Filter.Tendsto (fun lam : ℝ =>
      TeleDriving.ScarceFleet.SL (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (TeleDriving.ScarceFleet.mLam alpha s lam) -
        TeleDriving.ScarceFleet.SL (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) ⌊(1 + delta) * q3 lam⌋₊)
      Filter.atTop (nhds 0) := by sorry

end TeleDriving.AsymRich
