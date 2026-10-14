-- Prove2me | Theorems.Thm_TeleDriving_ScarceFleet_appC1_condition5_iff
-- name    : TeleDriving.ScarceFleet.appC1_condition5_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:30.65416+00:00
-- url     : https://prove2.me/theorems/2aa19380-3a4d-44d2-912d-14087e265aa5
-- title:
--   App. C.1, p. 40 — π_{m,m}(m) > π_{m,m−1}(m−1) if and only if Condition (5): λSL(m, m) > mµ(m, m)
-- statement:
--   Under Assumptions 1–2 and the size restriction, the probability that all drivers are busy is larger with $m$ drivers than with $m - 1$ drivers exactly when Condition (5) holds:
--   $$\pi_{m,m}(m) > \pi_{m,m-1}(m-1) \iff \lambda\, SL(m,m) > m\,\mu(m,m).$$
--
--   Condition (5) compares the average trip-completion rate $\lambda SL(m,m)$ with the completion rate $m\mu(m,m)$ when every vehicle is occupied. By the dichotomy of App. C.1 it decides which of the two shapes the service level has, which is how Theorem 1.A is proved.
--
--   **Formalization Note** $m - 1$ is natural-number subtraction; the standing hypotheses force $m \ge 2$ (Assumption 2 places a turning point strictly inside $(1, m)$). $\pi_{m,m-1}(m-1)$ is the blocking probability of the system with $m$ vehicles and $m - 1$ drivers.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. C.1, p. 40 (the display for SL(m, n+1) and the sentence after it)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.ScarceFleet

theorem appC1_condition5_iff (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hA2 : Assumption2 mu mbar) (hsize : StandingSize mu s mbar m lam) :
    piMN mu lam m m m > piMN mu lam m (m - 1) (m - 1) ↔
      lam * SL mu lam m m > (m : ℝ) * mu m (m : ℝ) := by sorry

end TeleDriving.ScarceFleet
