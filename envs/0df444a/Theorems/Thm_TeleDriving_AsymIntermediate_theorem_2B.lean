-- Prove2me | Theorems.Thm_TeleDriving_AsymIntermediate_theorem_2B
-- name    : TeleDriving.AsymIntermediate.theorem_2B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:57.586376+00:00
-- url     : https://prove2.me/theorems/dd583c9a-f9f4-4ad5-8f29-27ba0ffd8be0
-- title:
--   Theorem 2.B, p. 22 — for m_λ = ⌊αλs⌋ with α ∈ (1, 2), max_n SL(m_λ, n)/SL(m_λ, m_λ) → 1
-- statement:
--   Consider the ride-hailing system with arrival rate $\lambda$ and the service rate (4),
--   $$\mu(m,q) = \left[\frac{s}{\sqrt{m-q+1}} + s\right]^{-1}, \qquad s > 0,$$
--   and scale the fleet with demand as $m_\lambda = \lfloor \alpha\lambda s\rfloor$ for a fixed $\alpha \in (1,2)$. Let $SL(m,n)$ be the service level with $m$ vehicles and $n$ remote drivers. Then
--   $$\lim_{\lambda\to\infty}\left[\max_{n\in\{1,\dots,m_\lambda\}} \frac{SL(m_\lambda,n)}{SL(m_\lambda,m_\lambda)}\right] = 1 .$$
--
--   For $\alpha \in (1,2)$ the system is in the intermediate regime. The theorem says that choosing the number of remote drivers optimally improves the service level over the system with one driver per vehicle by a factor that tends to one: in a large intermediate market, remote drivers bring no asymptotic service-level gain. It sits between Theorem 2.A (supply-limited, gain of at least $2-\alpha$) and Theorem 2.C (supply-rich).
--
--   **Formalization Note** $m_\lambda$ uses the natural-number floor and $\lambda \to \infty$ along the reals. The maximum over $n \in \{1,\dots,m_\lambda\}$ is a supremum over a finite index set, so it is attained; for the small $\lambda$ with $m_\lambda = 0$ (that is, $\alpha\lambda s < 1$) it takes the junk value $0$, which does not affect the limit. Nothing is assumed about the service levels or the stationary distribution.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 22, Theorem 2.B; proof App. D.2, pp. 46–47

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymIntermediate

theorem theorem_2B (s alpha : ℝ) (hs : 0 < s) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    Filter.Tendsto (fun lam : ℝ => TeleDriving.ScarceFleet.maxSLRatio (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam))
      Filter.atTop (nhds 1) := by sorry

end TeleDriving.AsymIntermediate
