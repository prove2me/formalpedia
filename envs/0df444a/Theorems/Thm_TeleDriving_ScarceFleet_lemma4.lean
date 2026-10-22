-- Prove2me | Theorems.Thm_TeleDriving_ScarceFleet_lemma4
-- name    : TeleDriving.ScarceFleet.lemma4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:31.137902+00:00
-- url     : https://prove2.me/theorems/c60c0a88-a444-408a-94b8-d96f06e58737
-- title:
--   Lemma 4, p. 39 — π_{m,n−1}(n−1) > π_{m,n}(n) iff either side exceeds (ρ(n)−1)/ρ(n)
-- statement:
--   Under Assumptions 1–2 and the size restriction, write $\pi_{m,n}(n)$ for the stationary probability that all $n$ drivers are busy in the system with $m$ vehicles and $n$ remote drivers. For every $n \in \{1, \dots, m\}$, the following are equivalent:
--   $$\pi_{m,n-1}(n-1) > \pi_{m,n}(n) \iff \pi_{m,n-1}(n-1) > \frac{\rho(n)-1}{\rho(n)} \iff \pi_{m,n}(n) > \frac{\rho(n)-1}{\rho(n)}.$$
--
--   The lemma turns the comparison of the blocking probabilities of consecutive driver counts into a comparison with the explicit threshold $1 - 1/\rho(n)$, which is the recursion used in the proofs of Theorems 1.A–1.C.
--
--   **Formalization Note** The statement is the paper's pair of equivalences. At $n = 1$ the left side is $\pi_{m,0}(0) = 1$ (empty sum and product), as (2) also gives. The proof on the page assumes "$a, b, c, d > 0$", where $c = [\rho(n) - 1]\prod_{q<n}\rho(q)$ can be negative; the lemma holds regardless (only $b, d > 0$ is needed), and no such hypothesis is added.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 39, Lemma 4; proof p. 39, (11)–(12)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.ScarceFleet

theorem lemma4 (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hA2 : Assumption2 mu mbar) (hsize : StandingSize mu s mbar m lam)
    (n : ℕ) (hn1 : 1 ≤ n) (hnm : n ≤ m) :
    (piMN mu lam m (n - 1) (n - 1) > piMN mu lam m n n ↔
        piMN mu lam m (n - 1) (n - 1) > (rho mu lam m (n : ℝ) - 1) / rho mu lam m (n : ℝ)) ∧
      (piMN mu lam m (n - 1) (n - 1) > piMN mu lam m n n ↔
        piMN mu lam m n n > (rho mu lam m (n : ℝ) - 1) / rho mu lam m (n : ℝ)) := by sorry

end TeleDriving.ScarceFleet
