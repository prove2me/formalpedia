-- Prove2me | Theorems.Thm_TeleDriving_AmpleFleet_appC3_pi_strictAnti
-- name    : TeleDriving.AmpleFleet.appC3_pi_strictAnti
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:39.849976+00:00
-- url     : https://prove2.me/theorems/f6bb6db6-699e-4731-9511-91ed722d994f
-- title:
--   App. C.3, p. 41 — in the supply-rich regime π_{m,n}(n) is strictly decreasing in n ∈ {1, …, m}
-- statement:
--   In the ride-hailing loss model under Assumptions 1–2 and the size restriction, suppose the system is supply-rich ($\lambda < m\,\mu(m,m)$), and let $q_3 \in [1,m]$ be the root of Lemma 3(iii): $\rho(q_3) = 1$ and, for $q \in [1,m]$, $\rho(q) < 1$ exactly when $q > q_3$. Then the probability that all drivers are busy,
--
--   $$n \longmapsto \pi_{m,n}(n), \qquad n \in \{1,\dots,m\},$$
--
--   is strictly decreasing.
--
--   This is the content of the first part of Theorem 1.C: adding remote drivers always lowers the blocking probability when vehicles are ample.
--
--   **Formalization Note** The paper argues separately for $1 \le n < q_3$ and $q_3 < n \le m$; the statement covers the whole range $\{1,\dots,m\}$, including the step across $q_3$. "Decreasing" is strict, as the proof gives. $q_3$ is a variable carrying its Lemma 3(iii) characterization, not a hypothesis about monotonicity.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 41, App. C.3 (first paragraph), citing steps (i)–(ii) of App. C.2, pp. 40–41

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AmpleFleet

theorem appC3_pi_strictAnti (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : TeleDriving.ScarceFleet.Assumption1 mu s)
    (hA2 : TeleDriving.ScarceFleet.Assumption2 mu mbar) (hsize : TeleDriving.ScarceFleet.StandingSize mu s mbar m lam)
    (hreg : TeleDriving.ScarceFleet.IsSupplyRich mu lam m) (q3 : ℝ)
    (hq3 : q3 ∈ Set.Icc (1 : ℝ) m ∧ TeleDriving.ScarceFleet.rho mu lam m q3 = 1 ∧
      ∀ q ∈ Set.Icc (1 : ℝ) m, (TeleDriving.ScarceFleet.rho mu lam m q < 1 ↔ q3 < q)) :
    StrictAntiOn (fun n : ℕ => TeleDriving.ScarceFleet.piMN mu lam m n n) (Set.Icc 1 m) := by sorry

end TeleDriving.AmpleFleet
