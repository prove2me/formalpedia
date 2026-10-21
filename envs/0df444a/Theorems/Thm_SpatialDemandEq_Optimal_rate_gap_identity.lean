-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_rate_gap_identity
-- name    : SpatialDemandEq.Optimal.rate_gap_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:04.245369+00:00
-- url     : https://prove2.me/theorems/9c8fcc59-6177-4a9f-84b6-0e82b96fb292
-- title:
--   Proof of Theorem 6, p. 19 — under the rates (17), 1/(μ_k − λA_k) = 1/(B − λ)(Σ_j √A_j) 1/√A_k
-- statement:
--   Let $\lambda < B$ and let $A_1,\dots,A_K > 0$. With the rates (17),
--   $$\mu_k = \lambda A_k + (B - \lambda)\frac{\sqrt{A_k}}{\sum_j \sqrt{A_j}},$$
--   one has, for every $k$,
--   $$\frac{1}{\mu_k - \lambda A_k} = \frac{1}{B - \lambda}\Big(\sum_j \sqrt{A_j}\Big)\frac{1}{\sqrt{A_k}}.$$
--
--   Multiplied by $c$, the right-hand side is the Voronoi weight (16) of Theorem 5 and the left-hand side is the decentralized waiting cost $f_k(A_k)$; this identity is what turns the optimality condition (24) into the equilibrium condition (1) in the proof of Theorem 6.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 19, proof of Theorem 6 (the identity after (24), using (17))

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem rate_gap_identity {K : ℕ} (lam B : ℝ) (hB : lam < B) (a : Fin K → ℝ)
    (ha : ∀ k, 0 < a k) (k : Fin K) :
    1 / (optRates lam B a k - lam * a k) =
      1 / (B - lam) * (∑ j, Real.sqrt (a j)) * (1 / Real.sqrt (a k)) := by sorry

end SpatialDemandEq.Optimal
