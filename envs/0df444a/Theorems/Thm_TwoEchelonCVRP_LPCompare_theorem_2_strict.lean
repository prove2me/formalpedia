-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LPCompare_theorem_2_strict
-- name    : TwoEchelonCVRP.LPCompare.theorem_2_strict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:42.390204+00:00
-- url     : https://prove2.me/theorems/6e56df93-66b8-45fd-a737-64aa957b5a0f
-- title:
--   Theorem 2 (second clause) — the inequality $z(RF(\beta,\lambda,\mu)) \ge z(LF)$ can be strict
-- statement:
--   There exist a 2E-CVRP instance, route families $\mathcal M$, $\mathcal R$, and an admissible choice of $(\beta, \lambda, \mu, \mu_0)$ (that is, $\mu_k \le 0$, $\mu_0 \le 0$ and $\beta$ a solution of (12)) such that $RF(\beta,\lambda,\mu)$ is feasible and
--   $$z(LF) < z(RF(\beta, \lambda, \mu)) < +\infty.$$
--
--   This is the second half of Theorem 2: the relaxation $RF$ can be strictly stronger than the LP relaxation.
--
--   **Formalization Note.** The instance must satisfy every structural requirement of the model (positive demands, $0 < Q_2 < Q_1$, $m^2 \le \sum_k m_k$, route loads at most $Q_2$). The clause $z(RF) < +\infty$ is added so that the strict gap cannot come from an infeasible $RF$.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 301, Theorem 2 (second clause)

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LPCompare_Relaxations

namespace TwoEchelonCVRP.LPCompare

/-- **Theorem 2, second clause (Baldacci et al. 2013, p. 301).** The inequality
`max_{β,λ,μ} z(RF(β, λ, μ)) ≥ z(LF)` can be strict: there are an instance, a route system and
an admissible penalty choice with `z(LF) < z(RF(β, λ, μ))`, where moreover `RF` is feasible
(`z(RF(β, λ, μ)) < ⊤`), so the gap is not produced by an infeasible `RF`. -/
theorem theorem_2_strict :
    ∃ (I : Instance) (RS : RouteSystem I) (beta : Fin I.nc → Fin I.ns → ℝ)
      (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ),
      Admissible RS beta lam mu mu0 ∧ zLF RS < zRF RS beta lam mu mu0 ∧
        zRF RS beta lam mu mu0 < ⊤ := by sorry

end TwoEchelonCVRP.LPCompare
