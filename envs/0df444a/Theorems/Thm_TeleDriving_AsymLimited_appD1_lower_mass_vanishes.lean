-- Prove2me | Theorems.Thm_TeleDriving_AsymLimited_appD1_lower_mass_vanishes
-- name    : TeleDriving.AsymLimited.appD1_lower_mass_vanishes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:36.845075+00:00
-- url     : https://prove2.me/theorems/d9e4d35d-5937-499f-9886-b43d3f1c3d42
-- title:
--   App. D.1, (21), pp. 45–46 — Σ_{i=0}^{⌊(1−ϵ)n*⌋} π_{m_λ,⌊n*⌋}(i) → 0
-- statement:
--   Let $s > 0$, $\alpha \in (0,1)$, the service rate be (4), $m_\lambda = \lfloor\alpha\lambda s\rfloor$, and $H(n) = 1/\rho(n)$ for $m = m_\lambda$. Let $n^*(\lambda)$ be a maximizer of $H$ on $[0,m_\lambda]$, for all sufficiently large $\lambda$. Then for every $\epsilon \in (0,1)$,
--   $$\lim_{\lambda\to\infty}\ \sum_{i=0}^{\lfloor(1-\epsilon)n^*\rfloor}\pi_{m_\lambda,\lfloor n^*\rfloor}(i) = 0.$$
--
--   With $\lfloor n^*\rfloor$ remote drivers, the stationary mass sits asymptotically in the top fraction $\epsilon$ of occupancy levels; this localizes the blocking probability $\pi_{m_\lambda,\lfloor n^*\rfloor}(\lfloor n^*\rfloor)$ and leads to the bound (22).
--
--   **Formalization Note** $n^*$ is a function of $\lambda$ characterized by a hypothesis that holds eventually (for small $\lambda$, $m_\lambda \le 4$ and the maximizer is not the page's object). The floors are natural-number floors. The $\epsilon$ here is the page's cut-off $\epsilon$ in $(1-\epsilon)n^*$, written `eps` in Lean.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.1, (21), pp. 45–46

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model
import Definitions.Def_TeleDriving_AsymLimited_Aux

namespace TeleDriving.AsymLimited

theorem appD1_lower_mass_vanishes (s alpha : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (nstar : ℝ → ℝ)
    (hn : ∀ᶠ lam in Filter.atTop,
      nstar lam ∈ Set.Icc (0 : ℝ) (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) ∧
      IsMaxOn (H s lam (TeleDriving.ScarceFleet.mLam alpha s lam)) (Set.Icc (0 : ℝ) (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ)) (nstar lam))
    (eps : ℝ) (heps0 : 0 < eps) (heps1 : eps < 1) :
    Filter.Tendsto
      (fun lam : ℝ => ∑ i ∈ Finset.range (⌊(1 - eps) * nstar lam⌋₊ + 1),
        TeleDriving.ScarceFleet.piMN (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) ⌊nstar lam⌋₊ i)
      Filter.atTop (nhds 0) := by sorry

end TeleDriving.AsymLimited
