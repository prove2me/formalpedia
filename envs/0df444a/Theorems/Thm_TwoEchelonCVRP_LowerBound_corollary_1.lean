-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LowerBound_corollary_1
-- name    : TwoEchelonCVRP.LowerBound.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:30.397221+00:00
-- url     : https://prove2.me/theorems/59305019-6c9a-4b85-8158-fd03b9bbc14f
-- title:
--   Corollary 1 — routes with c̃_kl ≥ z(UB) − z(RF) are absent from every solution cheaper than z(UB)
-- statement:
--   Consider a 2E-CVRP instance with positive demands and route families $\mathcal M$, $\mathcal R$. Let $\lambda \in \mathbb R^{N_C}$, $\mu_k \le 0$, $\mu_0 \le 0$, let $\beta$ satisfy (12), and let
--   $$\tilde c_{kl} = c_{kl} - \sum_{i \in N_C} a_{ikl}(\beta_{ik} + \lambda_i) - \mu_k - \mu_0$$
--   be the reduced cost of the second-level route $l \in \mathcal R_k$. Let $z(\mathrm{UB})$ be a real number. Then every feasible solution of $F$ of cost smaller than $z(\mathrm{UB})$ uses no second-level route $l$ with $\tilde c_{kl} \ge z(\mathrm{UB}) - z(RF(\beta,\lambda,\mu))$; that is, every route $l$ it uses satisfies
--   $$\tilde c_{kl} + z(RF(\beta,\lambda,\mu)) < z(\mathrm{UB}).$$
--
--   Reduced-cost fixing of this kind shrinks the route sets before the exact phase of the method.
--
--   **Formalization Note** The paper assumes $z(\mathrm{UB})$ is a valid upper bound and speaks of optimal solutions; neither is used, so the statement is given for any real $z(\mathrm{UB})$ and every feasible solution cheaper than it (a strengthening). The inequality is written with an addition because $z(RF)$ is an extended real.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 301, Corollary 1

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model
import Definitions.Def_TwoEchelonCVRP_LowerBound_RF

namespace TwoEchelonCVRP.LowerBound

/-- Corollary 1 (p. 301): if `β` solves (12) and `μ ≤ 0`, `μ_0 ≤ 0`, then a feasible solution of F
of cost smaller than `zUB` uses no second-level route `l` with `c̃_l ≥ zUB − z(RF(β, λ, μ))`;
stated without subtraction as `c̃_l + z(RF) < zUB` for every used route. -/
theorem corollary_1 (I : Instance) (RS : RouteSystem I)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (zUB : ℝ) (s : SolF RS) (hs : IsFeasibleF RS s) (hcost : costF RS s < zUB)
    (l : RS.SR) (hl : s.x l = true) :
    ((reducedCost RS β lam μ μ0 l : ℝ) : EReal) + zRF RS β lam μ μ0 < ((zUB : ℝ) : EReal) := by sorry

end TwoEchelonCVRP.LowerBound
