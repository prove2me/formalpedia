-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LowerBound_theorem_4
-- name    : TwoEchelonCVRP.LowerBound.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:45.237052+00:00
-- url     : https://prove2.me/theorems/6bdfcd76-848a-449e-a817-9cffa6113ad9
-- title:
--   Theorem 4 — the marginal costs (24) over non-elementary routes solve the penalty system (12)
-- statement:
--   Consider a 2E-CVRP instance with positive demands and route families $\mathcal M$, $\mathcal R$, and let $\hat{\mathcal R}_k \supseteq \mathcal R_k$ be enlarged families of not necessarily elementary routes. For any penalties $\lambda \in \mathbb R^{N_C}$, $\mu \in \mathbb R^{N_S}$, $\mu_0 \in \mathbb R$, the vector $\beta$ given by
--   $$\beta_{ik} = q_i \min_{l \in \hat{\mathcal R}_{ik}} \left\{ \frac{c_{kl} - \sum_{i' \in N_C} a_{i'kl}\lambda_{i'} - \mu_k - \mu_0}{\sum_{i' \in N_C} a_{i'kl}q_{i'}} \right\} \qquad (24)$$
--   is a feasible solution of the penalty system (12):
--   $$\sum_{i \in N_C} a_{ikl}\beta_{ik} \le c_{kl} - \sum_{i \in N_C} a_{ikl}\lambda_i - \mu_k - \mu_0 \qquad \text{for every } l \in \mathcal R_k,\ k \in N_S .$$
--
--   This is how the paper's bounding procedure produces, at every step, a $\beta$ to which Theorems 1 and 3 apply.
--
--   **Formalization Note** The paper takes $\mu_k, \mu_0 \le 0$; the statement holds for all real penalties, so the sign conditions are not assumed. $\beta_{ik}$ is $0$ when $\hat{\mathcal R}_{ik}$ is empty, a value that does not enter (12).
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 302, Theorem 4, Eq. (24)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model
import Definitions.Def_TwoEchelonCVRP_LowerBound_RF
import Definitions.Def_TwoEchelonCVRP_LowerBound_ExtRoutes

namespace TwoEchelonCVRP.LowerBound

/-- Theorem 4 (p. 302): for any enlarged family `𝓡̂_k ⊇ 𝓡_k` of not necessarily elementary routes,
the marginal costs `β_{ik}` of (24) solve the penalty system (12). -/
theorem theorem_4 (I : Instance) (RS : RouteSystem I) (E : ExtRoutes RS)
    (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ) :
    SatisfiesPenalty RS (E.beta24 lam μ μ0) lam μ μ0 := by sorry

end TwoEchelonCVRP.LowerBound
