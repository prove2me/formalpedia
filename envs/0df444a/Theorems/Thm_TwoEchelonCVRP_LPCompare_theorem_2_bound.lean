-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LPCompare_theorem_2_bound
-- name    : TwoEchelonCVRP.LPCompare.theorem_2_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:57.823863+00:00
-- url     : https://prove2.me/theorems/5591e3a2-881f-414f-8142-164f2e636a4a
-- title:
--   Theorem 2 (first clause) — some admissible $(\beta,\lambda,\mu)$ gives $z(RF(\beta,\lambda,\mu)) \ge z(LF)$
-- statement:
--   Let a 2E-CVRP instance and route families $\mathcal M$, $\mathcal R$ be given, and suppose the LP relaxation $LF$ of formulation $F$ has a feasible point. Then there are penalties $\lambda \in \mathbb{R}^{N_C}$, $\mu_k \le 0$ ($k \in N_S$), $\mu_0 \le 0$ and marginal costs $\beta$ satisfying inequalities (12) such that
--   $$z(LF) \le z(RF(\beta, \lambda, \mu)).$$
--   Consequently $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)) \ge z(LF)$, the maximum being over admissible choices.
--
--   This is the first half of Theorem 2: the best bound obtainable from the relaxation $RF$ is never weaker than the LP relaxation bound.
--
--   **Formalization Note.** The feasibility of $LF$ is assumed. If $LF$ is infeasible then $z(LF) = +\infty$, and there are instances where every admissible choice gives a finite $z(RF)$, so no single choice attains the value; the printed "max" is read as attained only when $LF$ is feasible.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 301, Theorem 2 (first clause)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LPCompare_Relaxations

namespace TwoEchelonCVRP.LPCompare

/-- **Theorem 2, first clause (Baldacci et al. 2013, p. 301).** For every instance and route
system whose LP relaxation `LF` is feasible, some admissible penalty choice `(β, λ, μ, μ₀)`
(`μ ≤ 0`, `μ₀ ≤ 0`, `β` a solution of (12)) gives `z(LF) ≤ z(RF(β, λ, μ))`; hence
`max_{β,λ,μ} z(RF(β, λ, μ)) ≥ z(LF)`. -/
theorem theorem_2_bound (I : Instance) (RS : RouteSystem I)
    (hLF : ∃ p : LFPoint RS, IsFeasibleLF p) :
    ∃ (beta : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ),
      Admissible RS beta lam mu mu0 ∧ zLF RS ≤ zRF RS beta lam mu mu0 := by sorry

end TwoEchelonCVRP.LPCompare
