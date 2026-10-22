-- Prove2me | Theorems.Thm_TeleDriving_AmpleFleet_lemma4
-- name    : TeleDriving.AmpleFleet.lemma4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:36.701639+00:00
-- url     : https://prove2.me/theorems/786cec7e-e75a-4fa7-8ae9-5cc4017f9792
-- title:
--   Lemma 4, p. 39 — π_{m,n−1}(n−1) > π_{m,n}(n) iff either side exceeds (ρ(n)−1)/ρ(n)
-- statement:
--   In the ride-hailing loss model under Assumptions 1–2 and the size restriction, let $\pi_{m,n}(n)$ be the stationary probability that all $n$ drivers are busy. For every $n \in \{1,\dots,m\}$,
--
--   $$\pi_{m,n-1}(n-1) > \pi_{m,n}(n) \iff \pi_{m,n-1}(n-1) > \frac{\rho(n)-1}{\rho(n)} \iff \pi_{m,n}(n) > \frac{\rho(n)-1}{\rho(n)} .$$
--
--   The lemma turns the comparison of consecutive blocking probabilities into a comparison with a threshold depending only on $\rho(n)$; it drives every monotonicity argument for the service level $SL(m,n) = 1 - \pi_{m,n}(n)$ in the number of drivers.
--
--   **Formalization Note** At $n = 1$ the left side is $\pi_{m,0}(0) = 1$ (empty sum and product), as in (2). The two equivalences are stated as two conjuncts with a common left side.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 39, Lemma 4

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AmpleFleet

theorem lemma4 (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : TeleDriving.ScarceFleet.Assumption1 mu s)
    (hA2 : TeleDriving.ScarceFleet.Assumption2 mu mbar) (hsize : TeleDriving.ScarceFleet.StandingSize mu s mbar m lam)
    (n : ℕ) (hn1 : 1 ≤ n) (hnm : n ≤ m) :
    (TeleDriving.ScarceFleet.piMN mu lam m (n - 1) (n - 1) > TeleDriving.ScarceFleet.piMN mu lam m n n ↔
        TeleDriving.ScarceFleet.piMN mu lam m (n - 1) (n - 1) > (TeleDriving.ScarceFleet.rho mu lam m (n : ℝ) - 1) / TeleDriving.ScarceFleet.rho mu lam m (n : ℝ)) ∧
      (TeleDriving.ScarceFleet.piMN mu lam m (n - 1) (n - 1) > TeleDriving.ScarceFleet.piMN mu lam m n n ↔
        TeleDriving.ScarceFleet.piMN mu lam m n n > (TeleDriving.ScarceFleet.rho mu lam m (n : ℝ) - 1) / TeleDriving.ScarceFleet.rho mu lam m (n : ℝ)) := by sorry

end TeleDriving.AmpleFleet
