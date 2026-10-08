-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LowerBound_theorem_3
-- name    : TwoEchelonCVRP.LowerBound.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:15.912396+00:00
-- url     : https://prove2.me/theorems/f4cba579-b82d-4d76-9452-8f847666fa5d
-- title:
--   Theorem 3 (corrected) — z(RF-bar) is at most the RF cost of every RF solution respecting the second-level fleets
-- statement:
--   Consider a 2E-CVRP instance with positive demands and route families $\mathcal M$, $\mathcal R$, and let $\beta$, $\lambda$, $\mu$, $\mu_0$ be arbitrary real vectors. Let $(\xi, y, q)$ be a feasible solution of $RF$ whose satellite loads respect the second-level fleets:
--   $$\sum_{i \in N_C} q_i\xi_{ik} \le m_k Q_2 \qquad \text{for every } k \in N_S .$$
--   Then
--   $$z(\overline{RF}(\beta,\lambda,\mu)) \le \sum_{k \in N_S}\sum_{i \in N_C}\beta_{ik}\xi_{ik} + \sum_{r \in \mathcal M} g_r y_r + \sum_{i \in N_C}\lambda_i + \sum_{k \in N_S} m_k\mu_k + m^2\mu_0 .$$
--
--   Every $RF$ solution induced by a feasible solution of $F$ satisfies the load condition, so this is the form in which the paper uses Theorem 3: combined with Theorem 1 it gives the lower bound LD1.
--
--   **Formalization Note** The paper states $z(\overline{RF}(\beta,\lambda,\mu)) \le z(RF(\beta,\lambda,\mu))$ for every solution $\beta$ of (12). As printed this is false: $RF$ does not limit a satellite's load by $m_kQ_2$, while the loads in $W_r$ are capped by $\sum_{k \in R_r} m_kQ_2$. With one satellite, two customers of demand 1, $Q_1 = 10$, $Q_2 = 1$, $m^1 = m^2 = m_1 = 1$, $B_1 = 10$, $RF$ is feasible but $W_r = \emptyset$, so $z(\overline{RF}) = +\infty$. The load hypothesis is the correction. Neither (12) nor the signs of $\mu$ are needed, so they are not assumed. Optimal values are infima in the extended reals.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 302, Theorem 3 (corrected)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model
import Definitions.Def_TwoEchelonCVRP_LowerBound_RF
import Definitions.Def_TwoEchelonCVRP_LowerBound_RFbar

namespace TwoEchelonCVRP.LowerBound

/-- Theorem 3 (p. 302), corrected: `z(RF-bar(β, λ, μ))` is at most the objective (13) of every
feasible solution of RF whose satellite loads satisfy `∑_i q_i ξ_{ik} ≤ m_k Q_2`. (As printed,
without the load condition, the inequality `z(RF-bar) ≤ z(RF)` fails.) -/
theorem theorem_3 (I : Instance) (RS : RouteSystem I)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (σ : SolRF RS) (hσ : IsFeasibleRF RS σ) (hload : ∀ k, σ.load k ≤ I.m k * I.Q2) :
    zRFbar RS β lam μ μ0 ≤ ((objRF RS β lam μ μ0 σ : ℝ) : EReal) := by sorry

end TwoEchelonCVRP.LowerBound
