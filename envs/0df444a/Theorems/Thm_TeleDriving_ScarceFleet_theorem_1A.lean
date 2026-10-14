-- Prove2me | Theorems.Thm_TeleDriving_ScarceFleet_theorem_1A
-- name    : TeleDriving.ScarceFleet.theorem_1A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:40.133778+00:00
-- url     : https://prove2.me/theorems/5968af02-5007-4667-bb6f-b9384a0325d2
-- title:
--   Theorem 1.A, p. 18 — for m < γ₁(λ), under (5) SL(m, n) rises then falls in n; otherwise it is non-decreasing
-- statement:
--   Consider the ride-hailing system with $m$ vehicles, $n \in \{1, \dots, m\}$ remote drivers, Poisson demand of rate $\lambda$ and state-dependent trip rate $\mu(m,q)$ satisfying Assumptions 1 and 2, with $m \ge \bar m$ and $\lambda > \max\{1/s, \max_{q \le \bar m} q\mu(\bar m, q)\}$. Suppose the system is supply-limited, $m < \gamma_1(\lambda)$, that is, $\rho(q) = \lambda/(q\mu(m,q)) > 1$ for every $q \in [1, m]$. Let $SL(m,n)$ be the service level.
--
--   1. If
--   $$\lambda\, SL(m,m) > m\,\mu(m,m), \qquad (5)$$
--   then there is a threshold $\tilde n_1$ with $1 \le \tilde n_1 \le m - 1$ such that $SL(m,n)$ is strictly increasing in $n$ for $1 \le n \le \tilde n_1$, non-increasing for $\tilde n_1 \le n \le m$, and strictly decreasing for $\tilde n_1 + 1 \le n \le m$.
--   2. Otherwise $SL(m,n)$ is non-decreasing in $n$ on $\{1, \dots, m\}$.
--
--   The theorem shows that with remote drivers, fewer drivers than vehicles can give a strictly higher service level, and that Condition (5) decides exactly when.
--
--   **Formalization Note** The regime $m < \gamma_1(\lambda)$ is encoded by its characterization in Lemma 3(i), $\rho(q) > 1$ on $[1, m]$, since an integer $m$ almost never solves the defining equation of $\gamma_1$. "Increasing … when $n \le \tilde n_1$ and decreasing … when $n > \tilde n_1$" is stated with the junction made explicit: $SL(m,\tilde n_1) \ge SL(m, \tilde n_1 + 1)$ is non-strict, because the proof (scenario (b) of App. C.1) only yields $\pi_{m,\tilde n_1}(\tilde n_1) \le \pi_{m,\tilde n_1+1}(\tilde n_1+1)$ there. The bound $1 \le \tilde n_1$ is added so that the threshold cannot be degenerate. $n$ ranges over $\{1, \dots, m\}$; $m - 1$ is natural-number subtraction (here $m \ge 2$).
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), p. 18, Theorem 1.A, (5); proof App. C.1, pp. 39–40

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.ScarceFleet

theorem theorem_1A (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hA2 : Assumption2 mu mbar) (hsize : StandingSize mu s mbar m lam)
    (hreg : IsSupplyLimited mu lam m) :
    (lam * SL mu lam m m > (m : ℝ) * mu m (m : ℝ) →
      ∃ n1 : ℕ, 1 ≤ n1 ∧ n1 ≤ m - 1 ∧
        StrictMonoOn (SL mu lam m) (Set.Icc 1 n1) ∧
        AntitoneOn (SL mu lam m) (Set.Icc n1 m) ∧
        StrictAntiOn (SL mu lam m) (Set.Icc (n1 + 1) m)) ∧
    (¬ (lam * SL mu lam m m > (m : ℝ) * mu m (m : ℝ)) →
      MonotoneOn (SL mu lam m) (Set.Icc 1 m)) := by sorry

end TeleDriving.ScarceFleet
