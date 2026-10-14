-- Prove2me | Theorems.Thm_TeleDriving_AsymRich_theorem_2C
-- name    : TeleDriving.AsymRich.theorem_2C
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:37.588987+00:00
-- url     : https://prove2.me/theorems/51c5a503-fb06-401b-ba2b-bbe99277f581
-- title:
--   Theorem 2.C, p. 22 — in the supply-rich regime α > 2, lim sup_{λ→∞} n*_λ / m_λ ≤ 1/α
-- statement:
--   Let $s > 0$ be the mean trip time, let the service rate be (4), $\mu(m,q) = [s/\sqrt{m-q+1} + s]^{-1}$, and scale the fleet with demand as $m_\lambda = \lfloor\alpha\lambda s\rfloor$ for a constant $\alpha > 2$ (the supply-rich regime). For a tolerance $\epsilon > 0$ let
--
--   $$n^*_\lambda = \min\{\, n \in \{1,\dots,m_\lambda\} : SL(m_\lambda, m_\lambda) - SL(m_\lambda, n) < \epsilon \,\}$$
--
--   be the smallest number of remote drivers whose service level is within $\epsilon$ of that of a system with one driver per vehicle. Then
--
--   $$\limsup_{\lambda\to\infty} \frac{n^*_\lambda}{m_\lambda} \le \frac{1}{\alpha}.$$
--
--   Since $\alpha > 2$, a large supply-rich tele-driving system can operate with at most about half as many drivers as vehicles, and the bound does not depend on $\epsilon$.
--
--   **Formalization Note** The $\limsup$ is stated in $\varepsilon$-form: for every $\delta > 0$, eventually in $\lambda$, $n^*_\lambda/m_\lambda \le 1/\alpha + \delta$. The minimum defining $n^*_\lambda$ ranges over $\{1,\dots,m_\lambda\}$ (the paper leaves the range implicit); it is attained since $n = m_\lambda$ qualifies. The tolerance $\epsilon > 0$ is arbitrary, as printed.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 22, Theorem 2.C with footnote 14 (pp. 22–23); proof App. D.3, pp. 47–48

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model
import Definitions.Def_TeleDriving_AsymRich_NStar

namespace TeleDriving.AsymRich

theorem theorem_2C (s alpha eps : ℝ) (hs : 0 < s) (ha : 2 < alpha) (heps : 0 < eps) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ lam in Filter.atTop,
      (nStar (TeleDriving.ScarceFleet.muBesbes s) lam eps (TeleDriving.ScarceFleet.mLam alpha s lam) : ℝ) / (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ≤
        1 / alpha + δ := by sorry

end TeleDriving.AsymRich
