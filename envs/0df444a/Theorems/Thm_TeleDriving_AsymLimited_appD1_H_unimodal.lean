-- Prove2me | Theorems.Thm_TeleDriving_AsymLimited_appD1_H_unimodal
-- name    : TeleDriving.AsymLimited.appD1_H_unimodal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:33.512984+00:00
-- url     : https://prove2.me/theorems/c74d7149-d44c-40ff-bc95-31b42ddc2024
-- title:
--   App. D.1, p. 45 — for m > 4, H(n) = 1/ρ(n) first increases then decreases on [0, m]
-- statement:
--   Let $s > 0$, $\lambda > 0$, and let $m > 4$ be an integer number of vehicles. With the service rate (4), define for real $n \in [0,m]$
--   $$H(n) = \frac{1}{\rho(n)} = \frac{n}{\lambda s\big(\frac{1}{\sqrt{m-n+1}}+1\big)}.$$
--   Then there is $n^* \in (0,m)$ such that $H$ is strictly increasing on $[0,n^*]$ and strictly decreasing on $[n^*,m]$. In particular $n^*$ is the unique maximizer of $H$ on $[0,m]$.
--
--   $H(n)$ is the throughput per unit of demand when $n$ customers are in service; its maximizer $n^*$ is the number of drivers the proof of Theorem 2.A selects.
--
--   **Formalization Note** The page states this for $m = m_\lambda$; the claim and its argument do not use the relation between $m$ and $\lambda$, so it is stated for every $m > 4$ and $\lambda > 0$. The page's closed form (20) of $n^*$ is not stated: it involves real cube roots of a negative number, which Lean's `Real.rpow` does not represent; $n^*$ is characterized as the turning point instead.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D.1, pp. 44–45

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model
import Definitions.Def_TeleDriving_AsymLimited_Aux

namespace TeleDriving.AsymLimited

theorem appD1_H_unimodal (s : ℝ) (hs : 0 < s) (lam : ℝ) (hlam : 0 < lam) (m : ℕ) (hm : 4 < m) :
    ∃ nstar ∈ Set.Ioo (0 : ℝ) m,
      StrictMonoOn (H s lam m) (Set.Icc 0 nstar) ∧
      StrictAntiOn (H s lam m) (Set.Icc nstar (m : ℝ)) := by sorry

end TeleDriving.AsymLimited
