-- Prove2me | Theorems.Thm_TeleDriving_AmpleFleet_appC3_pi_bound
-- name    : TeleDriving.AmpleFleet.appC3_pi_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:47.863452+00:00
-- url     : https://prove2.me/theorems/748e1813-7a23-480f-9fd7-4664d3bd6019
-- title:
--   App. C.3, p. 41 — for q₃ < n ≤ m, π_{m,n}(n) < 1/(n − ⌊q₃⌋)
-- statement:
--   In the ride-hailing loss model under Assumptions 1–2 and the size restriction, suppose the system is supply-rich ($\lambda < m\,\mu(m,m)$), and let $q_3 \in [1,m]$ be the root of Lemma 3(iii). Then for every number of drivers $n \in \{1,\dots,m\}$ with $n > q_3$,
--
--   $$\pi_{m,n}(n) < \frac{1}{n - \lfloor q_3 \rfloor}.$$
--
--   This is the estimate behind the second part of Theorem 1.C: the blocking probability decays at least like the reciprocal of the number of drivers beyond $\lfloor q_3 \rfloor$.
--
--   **Formalization Note** $\lfloor q_3 \rfloor$ is the natural-number floor; since $q_3 \ge 1$ and $n > q_3$, the denominator $n - \lfloor q_3 \rfloor$ is a positive integer, and it is computed in the reals. The page calls this "a lower bound for $\pi_{m,n}(n)$"; what it derives is the upper bound stated here.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 41, App. C.3 (second paragraph)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AmpleFleet

theorem appC3_pi_bound (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : TeleDriving.ScarceFleet.Assumption1 mu s)
    (hA2 : TeleDriving.ScarceFleet.Assumption2 mu mbar) (hsize : TeleDriving.ScarceFleet.StandingSize mu s mbar m lam)
    (hreg : TeleDriving.ScarceFleet.IsSupplyRich mu lam m) (q3 : ℝ)
    (hq3 : q3 ∈ Set.Icc (1 : ℝ) m ∧ TeleDriving.ScarceFleet.rho mu lam m q3 = 1 ∧
      ∀ q ∈ Set.Icc (1 : ℝ) m, (TeleDriving.ScarceFleet.rho mu lam m q < 1 ↔ q3 < q)) :
    ∀ n : ℕ, n ∈ Set.Icc 1 m → q3 < (n : ℝ) →
      TeleDriving.ScarceFleet.piMN mu lam m n n < 1 / ((n : ℝ) - (⌊q3⌋₊ : ℝ)) := by sorry

end TeleDriving.AmpleFleet
