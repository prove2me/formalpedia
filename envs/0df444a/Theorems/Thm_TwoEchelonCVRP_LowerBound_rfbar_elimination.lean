-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LowerBound_rfbar_elimination
-- name    : TwoEchelonCVRP.LowerBound.rfbar_elimination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:15:17.791783+00:00
-- url     : https://prove2.me/theorems/5f0ec4fd-4642-48ca-a117-5a5d1ba2b1c0
-- title:
--   §3.2, after Theorem 3 — routes with c̃_kl ≥ z(UB) − z(RF-bar) are absent from every solution cheaper than z(UB)
-- statement:
--   Consider a 2E-CVRP instance with positive demands and route families $\mathcal M$, $\mathcal R$. Let $\lambda \in \mathbb R^{N_C}$, $\mu_k \le 0$, $\mu_0 \le 0$, let $\beta$ satisfy (12), and let $\tilde c_{kl} = c_{kl} - \sum_i a_{ikl}(\beta_{ik} + \lambda_i) - \mu_k - \mu_0$ be the reduced costs. Let $z(\mathrm{UB})$ be a real number. Then every feasible solution of $F$ of cost smaller than $z(\mathrm{UB})$ uses no second-level route $l \in \mathcal R_k$ with
--   $$\tilde c_{kl} \ge z(\mathrm{UB}) - z(\overline{RF}(\beta,\lambda,\mu));$$
--   that is, every route $l$ it uses satisfies $\tilde c_{kl} + z(\overline{RF}(\beta,\lambda,\mu)) < z(\mathrm{UB})$.
--
--   This is the route-elimination test the paper applies with the bound of $\overline{RF}$, which is cheap to compute.
--
--   **Formalization Note** The paper speaks of optimal solutions of cost below a known upper bound; the statement is proved for every feasible solution of cost below $z(\mathrm{UB})$, and $z(\mathrm{UB})$ is any real number (whether it is an upper bound is not used): both are strengthenings. The inequality is written with an addition instead of a subtraction because $z(\overline{RF})$ is an extended real.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 302, §3.2, the paragraph after Theorem 3

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LowerBound_Model
import Definitions.Def_TwoEchelonCVRP_LowerBound_RF
import Definitions.Def_TwoEchelonCVRP_LowerBound_RFbar

namespace TwoEchelonCVRP.LowerBound

/-- §3.2, the sentence after Theorem 3 (p. 302): if `β` solves (12) and `μ ≤ 0`, `μ_0 ≤ 0`, a
feasible solution of F of cost smaller than `zUB` uses no second-level route `l` with
`c̃_l ≥ zUB − z(RF-bar(β, λ, μ))`; stated as `c̃_l + z(RF-bar) < zUB` for every used route. -/
theorem rfbar_elimination (I : Instance) (RS : RouteSystem I)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (zUB : ℝ) (s : SolF RS) (hs : IsFeasibleF RS s) (hcost : costF RS s < zUB)
    (l : RS.SR) (hl : s.x l = true) :
    ((reducedCost RS β lam μ μ0 l : ℝ) : EReal) + zRFbar RS β lam μ μ0
      < ((zUB : ℝ) : EReal) := by sorry

end TwoEchelonCVRP.LowerBound
