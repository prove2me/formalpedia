-- Prove2me | Theorems.Thm_TeleDriving_ScarceFleet_appC1_dichotomy
-- name    : TeleDriving.ScarceFleet.appC1_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:33.625515+00:00
-- url     : https://prove2.me/theorems/4230b216-9220-4d13-9bdb-2d6967005172
-- title:
--   App. C.1, pp. 39–40 — π_{m,n}(n) is decreasing in n on {1,…,m}, or first decreasing and then increasing
-- statement:
--   Under Assumptions 1–2 and the size restriction, let $p(n) = \pi_{m,n}(n)$ be the probability that all $n$ remote drivers are busy, for $n \in \{1, \dots, m\}$. Then one of two shapes occurs (they exclude each other):
--
--   1. (scenario (a)) $p$ is strictly decreasing on $\{1, \dots, m\}$; or
--   2. (scenario (b)) there is $\tilde n_1$ with $1 \le \tilde n_1$ and $\tilde n_1 + 1 \le m$ such that $p$ is strictly decreasing on $\{1, \dots, \tilde n_1\}$,
--   $$p(\tilde n_1) \le p(\tilde n_1 + 1),$$
--   and $p$ is strictly increasing on $\{\tilde n_1 + 1, \dots, m\}$.
--
--   Since $SL(m,n) = 1 - p(n)$, this says that the service level is either increasing in the number of drivers or first increasing and then decreasing; it is the core of the proofs of Theorems 1.A and 1.B.
--
--   **Formalization Note** No regime hypothesis is made: the argument of App. C.1 never uses $m < \gamma_1(\lambda)$, and the same dichotomy serves Theorem 1.B in the intermediate regime. The case $\tilde n_1 = 1$ is allowed. The page's first sentence derives $p(2) < p(1)$ from "$\rho(1) > \rho(2)$ by Assumption 2", which Assumption 2 does not give; the dichotomy holds without it, so no hypothesis $p(2) < p(1)$ is added.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. C.1, pp. 39–40 (scenario split p. 39; steps (i)–(iii) and the summary p. 40)

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.ScarceFleet

theorem appC1_dichotomy (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hA2 : Assumption2 mu mbar) (hsize : StandingSize mu s mbar m lam) :
    StrictAntiOn (fun n : ℕ => piMN mu lam m n n) (Set.Icc 1 m) ∨
      ∃ k : ℕ, 1 ≤ k ∧ k + 1 ≤ m ∧
        StrictAntiOn (fun n : ℕ => piMN mu lam m n n) (Set.Icc 1 k) ∧
        piMN mu lam m k k ≤ piMN mu lam m (k + 1) (k + 1) ∧
        StrictMonoOn (fun n : ℕ => piMN mu lam m n n) (Set.Icc (k + 1) m) := by sorry

end TeleDriving.ScarceFleet
