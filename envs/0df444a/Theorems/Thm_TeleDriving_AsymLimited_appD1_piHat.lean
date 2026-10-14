-- Prove2me | Theorems.Thm_TeleDriving_AsymLimited_appD1_piHat
-- name    : TeleDriving.AsymLimited.appD1_piHat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:29.792781+00:00
-- url     : https://prove2.me/theorems/9e56dfcc-6c90-4188-8d26-3b93b9dd8a65
-- title:
--   App. D.1, (22), p. 46 — π̂ → 1 − (1 − ϵ)/a and π̂ > π_{m_λ,⌊n*⌋}(⌊n*⌋)
-- statement:
--   Let $s > 0$, $\alpha \in (0,1)$, $a = 1/\alpha$, the service rate be (4), $m_\lambda = \lfloor\alpha\lambda s\rfloor$, and $H(n) = 1/\rho(n)$ for $m = m_\lambda$. Let $n^*(\lambda)$ be a maximizer of $H$ on $[0,m_\lambda]$, for all sufficiently large $\lambda$, and fix $\epsilon \in (0,1)$. With $N = \lfloor n^*\rfloor$ and $z = \lfloor(1-\epsilon)n^*\rfloor$ let
--   $$\hat\pi_{m_\lambda,N}(N) = \pi_{m_\lambda,N}(N)\cdot\frac{1 + \sum_{i=0}^{N-z-1}\prod_{k=0}^{i}\frac{1}{\rho(N-k)}}{1 + \sum_{i=0}^{N-z-1}\big(\frac{1}{\rho(z)}\big)^{i+1}} \qquad (22).$$
--   Then:
--   1. $$\lim_{\lambda\to\infty}\hat\pi_{m_\lambda,N}(N) = 1 - \frac{1-\epsilon}{a};$$
--   2. for all sufficiently large $\lambda$, $\hat\pi_{m_\lambda,N}(N) > \pi_{m_\lambda,N}(N)$.
--
--   Since $SL(m_\lambda,N) = 1-\pi_{m_\lambda,N}(N)$, this gives an explicit asymptotic lower bound $(1-\epsilon)/a$ for the service level with $\lfloor n^*\rfloor$ drivers.
--
--   **Formalization Note** $n^*$ is characterized eventually, as in the previous milestone. The page states the strict inequality without qualification; it needs $N > z$, which holds for large $\lambda$, so it is stated eventually. $a$ is written `1 / alpha`.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.1, (22), p. 46

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model
import Definitions.Def_TeleDriving_AsymLimited_Aux

namespace TeleDriving.AsymLimited

theorem appD1_piHat (s alpha : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (nstar : ℝ → ℝ)
    (hn : ∀ᶠ lam in Filter.atTop,
      nstar lam ∈ Set.Icc (0 : ℝ) (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ∧
      IsMaxOn (H s lam (TeleDriving.ScarceFleet.mLam alpha s lam)) (Set.Icc (0 : ℝ) (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ)) (nstar lam))
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1) :
    Filter.Tendsto (fun lam : ℝ => piHat s alpha eps lam (nstar lam)) Filter.atTop
      (nhds (1 - (1 - eps) / (1 / alpha))) ∧
    (∀ᶠ lam in Filter.atTop,
      TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) ⌊nstar lam⌋₊ ⌊nstar lam⌋₊ <
        piHat s alpha eps lam (nstar lam)) := by sorry

end TeleDriving.AsymLimited
