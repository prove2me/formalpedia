-- Prove2me | Theorems.Thm_VehicleSharePricing_DemandFree_beta_increment_le
-- name    : VehicleSharePricing.DemandFree.beta_increment_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:41.174297+00:00
-- url     : https://prove2.me/theorems/3899a250-1308-413b-834d-34fa0d23d603
-- title:
--   Proof of Theorem 3, p. 11 — β(K) − β(K−1) ≤ β(1) = 1/(N+∆)
-- statement:
--   Let $N\ge1$ be an integer, $\Delta>0$, and $\beta(0)=0$, $\beta(K)=K/(N+K-1+\Delta(1-\beta(K-1)))$. Then for every $K\ge1$,
--
--   $$
--   \beta(K)-\beta(K-1)\le\beta(1)=\frac{1}{N+\Delta}.
--   $$
--
--   In the paper this follows from the concavity of $\beta$; it lets $\beta(K-1)$ be replaced by $\beta(K)-\frac1{N+\Delta}$ in the recursion, which produces a quadratic inequality in $\beta(K)$.
--
--   **Formalization Note** $K-1$ is natural-number subtraction under $K\ge1$.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 11, proof of Theorem 3

import Mathlib
import Definitions.Def_VehicleSharePricing_DemandFree_Beta

namespace VehicleSharePricing.DemandFree
theorem beta_increment_le (N : ℕ) (hN : 1 ≤ N) (Δ : ℝ) (hΔ : 0 < Δ) (K : ℕ) (hK : 1 ≤ K) :
    beta N Δ K - beta N Δ (K - 1) ≤ beta N Δ 1 ∧ beta N Δ 1 = 1 / ((N : ℝ) + Δ) := by sorry
end VehicleSharePricing.DemandFree
