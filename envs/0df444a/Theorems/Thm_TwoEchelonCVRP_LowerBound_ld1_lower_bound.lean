-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LowerBound_ld1_lower_bound
-- name    : TwoEchelonCVRP.LowerBound.ld1_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:14:23.292095+00:00
-- url     : https://prove2.me/theorems/0e7f4960-ff16-4dd4-8bcb-4b8d575d1a24
-- title:
--   Eq. (23) — LD1 = max over (β, λ, μ) of z(RF-bar) is a valid lower bound on the 2E-CVRP
-- statement:
--   Consider a 2E-CVRP instance with positive demands and route families $\mathcal M$, $\mathcal R$. Let $\lambda \in \mathbb R^{N_C}$, $\mu_k \le 0$ for every satellite $k$, $\mu_0 \le 0$, and let $\beta$ satisfy the penalty system (12). Then for every feasible solution $(x, y, q)$ of formulation $F$,
--   $$z(\overline{RF}(\beta,\lambda,\mu)) \le \sum_{k \in N_S}\sum_{l \in \mathcal R_k} c_{kl}x_{kl} + \sum_{r \in \mathcal M} g_r y_r .$$
--   Equivalently, the quantity
--   $$\mathrm{LD1} = \max_{\beta,\lambda,\mu}\{z(\overline{RF}(\beta,\lambda,\mu))\} \qquad (23)$$
--   is a valid lower bound on the 2E-CVRP, and so is every value of $z(\overline{RF})$ reached along the way.
--
--   This is the lower bound that the paper's bounding procedure DP¹ computes, and on which its route elimination and its configuration enumeration rest.
--
--   **Formalization Note** The bound is stated for every admissible $(\beta,\lambda,\mu)$, which is equivalent to $\mathrm{LD1} \le z(F)$ and avoids defining the maximum. $z(\overline{RF})$ is an infimum in the extended reals. The paper derives the bound from Theorem 1 and Theorem 3; Theorem 3 as printed is false (see the corrected milestone), but the bound itself holds because the $RF$ solutions induced by feasible solutions of $F$ respect the second-level fleets. Positive demands are needed: with a zero-demand customer the bound fails.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 302, Eq. (23), with Theorem 1 (p. 301) and Theorem 3 (p. 302)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model
import Definitions.Def_TwoEchelonCVRP_LowerBound_RF
import Definitions.Def_TwoEchelonCVRP_LowerBound_RFbar

namespace TwoEchelonCVRP.LowerBound

/-- Eq. (23) with Theorems 1 and 3 (pp. 301–302): `LD1 = max_{β,λ,μ} z(RF-bar(β, λ, μ))` is a valid
lower bound on the 2E-CVRP, i.e. for every solution `β` of (12) and every `λ`, `μ ≤ 0`, `μ_0 ≤ 0`,
`z(RF-bar(β, λ, μ))` is at most the cost of every feasible solution of F. -/
theorem ld1_lower_bound (I : Instance) (RS : RouteSystem I)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (s : SolF RS) (hs : IsFeasibleF RS s) :
    zRFbar RS β lam μ μ0 ≤ ((costF RS s : ℝ) : EReal) := by sorry

end TwoEchelonCVRP.LowerBound
