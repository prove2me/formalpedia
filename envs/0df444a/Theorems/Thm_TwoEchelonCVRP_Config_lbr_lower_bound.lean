-- Prove2me | Theorems.Thm_TwoEchelonCVRP_Config_lbr_lower_bound
-- name    : TwoEchelonCVRP.Config.lbr_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:53.960983+00:00
-- url     : https://prove2.me/theorems/733c090b-843f-4543-aed1-c5223e2eb5bc
-- title:
--   §5.1 — LB_R is a lower bound on the second-level routing cost
-- statement:
--   Let $\lambda\in\mathbb R^{N_C}$ be arbitrary, let $\mu_k\le0$ for every satellite $k$ and $\mu_0\le0$, and let $\beta$ satisfy the penalty system (12). Assume there is at least one satellite. Then for every feasible solution $(x,y,q)$ of formulation $F$,
--   $$\mathrm{LB}_R\le\sum_{k\in N_S}\sum_{l\in\mathcal R_k}c_{kl}x_{kl}.$$
--
--   The paper states this for optimal solutions; it holds for every feasible one. It is the bound used in condition (d) of Proposition 1.
--
--   **Formalization Note** The paper takes the specific penalties that produce the bound LD1; here any penalties with $\mu\le0$, $\mu_0\le0$ and (12) are allowed, a generalization.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 305, §5.1, the definition of LB_R

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Bounds

namespace TwoEchelonCVRP.Config

/-- §5.1, p. 305: for penalties `μ ≤ 0`, `μ_0 ≤ 0`, any `λ` and any `β` satisfying (12), `LB_R` is
at most the second-level routing cost `∑_{k ∈ N_S} ∑_{l ∈ 𝓡_k} c_{kl} x_{kl}` of every feasible
solution of F. -/
theorem lbr_lower_bound (I : Instance) (RS : RouteSystem I) (hns : 0 < I.ns)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (s : SolF RS) (hs : IsFeasibleF RS s) :
    LBR hns β lam μ μ0 ≤ secondLevelCost RS s := by sorry

end TwoEchelonCVRP.Config
