-- Prove2me | Theorems.Thm_VehicleSharePricing_DemandFree_beta_quadratic_bound
-- name    : VehicleSharePricing.DemandFree.beta_quadratic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:28.73024+00:00
-- url     : https://prove2.me/theorems/c9cf9f3d-882d-42f6-8670-8c83b1800be3
-- title:
--   Proof of Theorem 3, p. 11 — β(K) ≥ (N+K−1+∆+∆/(N+∆) − √((N+K−1+∆+∆/(N+∆))² − 4K∆))/(2∆)
-- statement:
--   Let $N\ge1$ be an integer, $\Delta>0$, and $\beta(0)=0$, $\beta(K)=K/(N+K-1+\Delta(1-\beta(K-1)))$. Write $b_K=N+K-1+\Delta+\frac{\Delta}{N+\Delta}$. Then for every $K\ge 1$,
--
--   $$
--   \beta(K)\ \ge\ \frac{b_K-\sqrt{b_K^{\,2}-4K\Delta}}{2\Delta}.
--   $$
--
--   The right-hand side is the smaller root of $\Delta x^2-b_Kx+K=0$; the bound states that $\beta(K)$ lies at or above it. At $\Delta=K$ it becomes the demand-free bound of Theorem 3.
--
--   **Formalization Note** The discriminant $b_K^2-4K\Delta$ is nonnegative because $\beta(K)$ satisfies $\Delta\beta(K)^2-b_K\beta(K)+K\le0$; so Lean's convention $\sqrt{x}=0$ for $x<0$ never enters.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 11, proof of Theorem 3

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Beta

namespace VehicleSharePricing.DemandFree
theorem beta_quadratic_bound (N : ℕ) (hN : 1 ≤ N) (Δ : ℝ) (hΔ : 0 < Δ) (K : ℕ) (hK : 1 ≤ K) :
    ((N : ℝ) + K - 1 + Δ + Δ / ((N : ℝ) + Δ) -
        Real.sqrt (((N : ℝ) + K - 1 + Δ + Δ / ((N : ℝ) + Δ)) ^ 2 - 4 * K * Δ)) / (2 * Δ)
      ≤ beta N Δ K := by sorry
end VehicleSharePricing.DemandFree
