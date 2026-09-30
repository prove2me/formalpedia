-- Prove2me | Theorems.Thm_RevenueManagement_deterministic_upper_bound
-- name    : RevenueManagement.deterministic_upper_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:48:59.640778+00:00
-- url     : https://prove2.me/theorems/48cc3a68-be33-45bd-a0b4-70f6386bf445
-- title:
--   Sect. 5.2.2.3: the optimal deterministic revenue (5.1) is an upper bound on the optimal expected revenue of the stochastic Bernoulli-demand model (5.12)
-- statement:
--   With a revenue rate concave in the demand rate on $[0, 1]$ (Assumption 7.2), the optimal
--   expected revenue $V_1(C)$ of the Bernoulli-demand model (5.12) with initial inventory
--   $C$ is at most the optimal value of the deterministic model (5.1), the maximum of
--   $\sum_{t=1}^{T} r(t, d(t))$ over rates $d(t) \in [0, 1]$ with $\sum_t d(t) \le C$.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 204-205, Sect. 5.2.2.3 ('the deterministic model (5.1) provides an upper bound on the expected revenue from the stochastic model'; proved there by the Lagrangian relaxation (5.14) for Bernoulli arrivals)

import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

theorem deterministic_upper_bound (p : ℕ → ℝ → ℝ) (T : ℕ)
    (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t)) (C : ℕ) :
    bernoulliValue p T 1 C ≤ deterministicValue p T 1 C := by sorry

end RevenueManagement
