-- Prove2me | Theorems.Thm_TeleDriving_AsymRich_appD_case_iii_unique_root
-- name    : TeleDriving.AsymRich.appD_case_iii_unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:54.348979+00:00
-- url     : https://prove2.me/theorems/6cd00c32-8a62-401b-a993-cf7737e3a350
-- title:
--   App. D, case (iii), p. 42 — for the rate (4) and m > 2λs, ρ(q) = 1 has a unique root q* in [λs, m]
-- statement:
--   Let $s > 0$ and $\lambda > 0$, and let the service rate be (4), $\mu(m,q) = [s/\sqrt{m-q+1} + s]^{-1}$, so that for $0 < q \le m$
--
--   $$\rho(q) = \frac{\lambda}{q}\Big(\frac{s}{\sqrt{m-q+1}} + s\Big). \qquad (13)$$
--
--   If the fleet size $m \in \mathbb N$ satisfies $m > 2\lambda s$, then there is a $q^* \in [\lambda s, m]$ such that
--
--   1. $\rho(q^*) = 1$;
--   2. $q^*$ is the only solution of $\rho(q) = 1$ in $[\lambda s, m]$;
--   3. for every $q \in (0, m]$, $\rho(q) < 1$ if and only if $q > q^*$.
--
--   This is case (iii) of the paper's analysis of the rate (4) (the supply-rich regime $m > \gamma_2(\lambda) = 2\lambda s$). The root $q^*$ equals the quantities $q_1 = q_3$ of the paper, the point beyond which the birth–death chain drifts downwards; the asymptotic results of the supply-rich regime are expressed through it.
--
--   **Formalization Note** The paper works with $RHS(q) = q/(\lambda s) - 1/\sqrt{m-q+1}$ and states "$RHS(q) < 1$ if $q < q^*$ and $RHS(q) \ge 1$ otherwise"; since $RHS(q) \le 1$ exactly when $\rho(q) \ge 1$ (for $0 < q \le m$), clause 3 is that sentence in terms of $\rho$. The point $q = 0$ is excluded because $\rho(0)$ is a junk value in Lean.
-- source:
--   Benjaafar, Wang & Yang, Human in The Loop Automation: Ride-Hailing with Remote (Tele-) Drivers, SSRN 4130757 (version of 1 June 2023), App. D, (13) and case (iii), p. 42

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

namespace TeleDriving.AsymRich

theorem appD_case_iii_unique_root (s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) (m : ℕ)
    (hm : 2 * lam * s < m) :
    ∃ q3 : ℝ, lam * s ≤ q3 ∧ q3 ≤ m ∧ TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam m q3 = 1 ∧
      (∀ q : ℝ, lam * s ≤ q → q ≤ m → TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam m q = 1 → q = q3) ∧
      ∀ q ∈ Set.Ioc (0 : ℝ) m, (TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam m q < 1 ↔ q3 < q) := by sorry

end TeleDriving.AsymRich
