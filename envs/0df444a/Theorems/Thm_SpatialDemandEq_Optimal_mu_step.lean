-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_mu_step
-- name    : SpatialDemandEq.Optimal.mu_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:00.587383+00:00
-- url     : https://prove2.me/theorems/e719bb95-4aa1-4a4e-9c6b-db8381585a9b
-- title:
--   Proof of Theorem 5, p. 18 — for fixed areas, the rates (17) minimize Σ A_k c/(μ_k − λA_k) under Σμ_k = B, with value c/(B−λ)(Σ√A_k)²
-- statement:
--   Fix constants $c > 0$, $0 < \lambda < B$ and areas $A_1,\dots,A_K > 0$ with $\sum_k A_k = 1$, and write $s = \sum_j \sqrt{A_j}$. Consider the rate problem (18) for a fixed partition: minimize
--   $$\sum_k A_k \frac{c}{\mu_k - \lambda A_k}$$
--   over rates $\mu$ with $\sum_k \mu_k = B$ and $\lambda A_k < \mu_k$ for every $k$. Let $\mu^\circ_k = \lambda A_k + (B - \lambda)\sqrt{A_k}/s$ be the rates (17). Then
--
--   1. $\mu^\circ$ is feasible: $\sum_k \mu^\circ_k = B$ and $\lambda A_k < \mu^\circ_k$ for all $k$;
--   2. its objective value is
--   $$\sum_k A_k \frac{c}{\mu^\circ_k - \lambda A_k} = \frac{c}{B - \lambda}\Big(\sum_k \sqrt{A_k}\Big)^2;$$
--   3. every other feasible $\mu \ne \mu^\circ$ has a strictly larger objective value.
--
--   This is the first step of the proof of Theorem 5: optimizing the service rates out of (15) leaves the partition problem (23) with the nonconvex $G(A) = \frac{c}{B-\lambda}\|A\|_{1/2}$.
--
--   **Formalization Note** The page derives the minimizer from the Lagrangian and states only the optimal value; the uniqueness clause 3 is part of the formal statement because Theorem 5's formula (17) for the rates needs it. The minimizer is also Kelly's square-root capacity allocation (Kelly 1979, Theorem 4.1, a referenced item of this mission) with arrival rates $\lambda A_k$, unit costs and budget $B$.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 18, proof of Theorem 5, equations (18)–(22) and the optimal objective value c/(B − λ)(Σ_k √A_k)²

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem mu_step {K : ℕ} (c lam B : ℝ) (hc : 0 < c) (hlam : 0 < lam) (hB : lam < B)
    (a : Fin K → ℝ) (ha : ∀ k, 0 < a k) (hsum : ∑ k, a k = 1) :
    (∑ k, optRates lam B a k = B ∧ ∀ k, lam * a k < optRates lam B a k) ∧
      rateCost c lam (optRates lam B a) a = c / (B - lam) * (∑ k, Real.sqrt (a k)) ^ 2 ∧
      ∀ μ : Fin K → ℝ, ∑ k, μ k = B → (∀ k, lam * a k < μ k) → μ ≠ optRates lam B a →
        rateCost c lam (optRates lam B a) a < rateCost c lam μ a := by sorry

end SpatialDemandEq.Optimal
