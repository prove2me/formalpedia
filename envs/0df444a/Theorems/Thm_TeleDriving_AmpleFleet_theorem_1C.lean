-- Prove2me | Theorems.Thm_TeleDriving_AmpleFleet_theorem_1C
-- name    : TeleDriving.AmpleFleet.theorem_1C
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:45.85444+00:00
-- url     : https://prove2.me/theorems/c22f1e75-e1d4-4b98-8f0b-193dd94132e4
-- title:
--   Theorem 1.C, pp. 20–21 — for m > γ₂(λ), SL(m, n) is increasing in n and exceeds 1 − 1/(n − ⌊q₃⌋) for n > q₃
-- statement:
--   Consider a ride-hailing system with $m$ vehicles and $n \le m$ remote drivers: customers arrive at Poisson rate $\lambda$, a request is lost when all drivers are busy, and with $q$ customers in service each is served at rate $\mu(m,q)$. Let $\rho(q) = \lambda/(q\,\mu(m,q))$ and let $SL(m,n) = 1 - \pi_{m,n}(n)$ be the service level, where $\pi_{m,n}$ is the stationary law (2)–(3). Assume Assumptions 1–2 and the size restriction $m \ge \bar m$, $\lambda > \max\{1/s, \max_{q \le \bar m} q\,\mu(\bar m,q)\}$.
--
--   Suppose the system is **supply-rich**, $m > \gamma_2(\lambda)$, i.e. $\rho(m) < 1$, and let $q_3$ be the unique root of $\rho = 1$ in $[1,m]$ of Lemma 3(iii) (Proposition 1). Then
--
--   1. $SL(m,n)$ is strictly increasing in $n \in \{1,\dots,m\}$;
--   2. for every $n \in \{1,\dots,m\}$ with $n > q_3$,
--
--   $$SL(m,n) > 1 - \frac{1}{n - \lfloor q_3 \rfloor}.$$
--
--   When vehicles are ample, removing a remote driver always costs service, but the cost is small once $n$ is well beyond $q_3$: the bound is increasing and concave in $n$, so the fleet of remote drivers can be cut below $m$ with little loss of service level.
--
--   **Formalization Note** The regime $m > \gamma_2(\lambda)$ is its characterization $\lambda < m\,\mu(m,m)$; $q_3$ is a real variable with the characterization of Lemma 3(iii) ($q_3 \in [1,m]$, $\rho(q_3) = 1$, and $\rho(q) < 1$ exactly for $q > q_3$ in $[1,m]$), which determines it uniquely and is satisfiable under the regime. The theorem says "increasing" and "lower bounded by"; both are stated strictly, which is what the paper's proof (App. C.3) derives. $\lfloor q_3 \rfloor$ is the natural-number floor and $n - \lfloor q_3 \rfloor$ is real subtraction.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), pp. 20–21, Theorem 1.C; proof App. C.3, p. 41

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AmpleFleet

theorem theorem_1C (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : TeleDriving.ScarceFleet.Assumption1 mu s)
    (hA2 : TeleDriving.ScarceFleet.Assumption2 mu mbar) (hsize : TeleDriving.ScarceFleet.StandingSize mu s mbar m lam)
    (hreg : TeleDriving.ScarceFleet.IsSupplyRich mu lam m) (q3 : ℝ)
    (hq3 : q3 ∈ Set.Icc (1 : ℝ) m ∧ TeleDriving.ScarceFleet.rho mu lam m q3 = 1 ∧
      ∀ q ∈ Set.Icc (1 : ℝ) m, (TeleDriving.ScarceFleet.rho mu lam m q < 1 ↔ q3 < q)) :
    StrictMonoOn (TeleDriving.ScarceFleet.SL mu lam m) (Set.Icc 1 m) ∧
      ∀ n : ℕ, n ∈ Set.Icc 1 m → q3 < (n : ℝ) →
        1 - 1 / ((n : ℝ) - (⌊q3⌋₊ : ℝ)) < TeleDriving.ScarceFleet.SL mu lam m n := by sorry

end TeleDriving.AmpleFleet
