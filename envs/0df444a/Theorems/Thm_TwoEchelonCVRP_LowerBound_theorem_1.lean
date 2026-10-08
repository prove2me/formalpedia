-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LowerBound_theorem_1
-- name    : TwoEchelonCVRP.LowerBound.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:48.10598+00:00
-- url     : https://prove2.me/theorems/7bb69270-feab-4f99-bb6f-2e02c1037973
-- title:
--   Theorem 1 — z(RF(β, λ, μ)) is a lower bound on the cost of every feasible 2E-CVRP solution
-- statement:
--   Consider a 2E-CVRP instance with positive demands and route families $\mathcal M$, $\mathcal R$. Let $\lambda \in \mathbb R^{N_C}$, $\mu_k \le 0$ for every $k \in N_S$ and $\mu_0 \le 0$, and let $\beta = (\beta_{ik})$ satisfy the penalty system (12). Then for every feasible solution $(x, y, q)$ of formulation $F$,
--   $$z(RF(\beta,\lambda,\mu)) \le \sum_{k \in N_S}\sum_{l \in \mathcal R_k} c_{kl}x_{kl} + \sum_{r \in \mathcal M} g_r y_r .$$
--   In words, $z(RF(\beta,\lambda,\mu))$ is a valid lower bound on the 2E-CVRP for any admissible choice of $(\beta,\lambda,\mu)$.
--
--   This is the first link in the chain that produces the paper's lower bound LD1; it also yields the reduced-cost elimination of Corollary 1.
--
--   **Formalization Note** The optimal value $z(RF)$ is an infimum in the extended reals ($+\infty$ if $RF$ is infeasible), and "valid lower bound" is stated as the inequality against every feasible solution of $F$, which is equivalent to $z(RF) \le z(F)$.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 301, Theorem 1

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model
import Definitions.Def_TwoEchelonCVRP_LowerBound_RF

namespace TwoEchelonCVRP.LowerBound

/-- Theorem 1 (p. 301): for any solution `β` of (12) and penalties `λ ∈ ℝ^{N_C}`,
`μ ∈ ℝ_−^{N_S+1}`, `z(RF(β, λ, μ))` is at most the cost of every feasible solution of F. -/
theorem theorem_1 (I : Instance) (RS : RouteSystem I)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (s : SolF RS) (hs : IsFeasibleF RS s) :
    zRF RS β lam μ μ0 ≤ ((costF RS s : ℝ) : EReal) := by sorry

end TwoEchelonCVRP.LowerBound
