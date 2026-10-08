-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LPCompare_theorem_2
-- name    : TwoEchelonCVRP.LPCompare.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:51.691871+00:00
-- url     : https://prove2.me/theorems/295c18fd-554f-489f-92c8-13cff410c905
-- title:
--   Theorem 2 — $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)) \ge z(LF)$, and the inequality can be strict
-- statement:
--   For the two-echelon capacitated vehicle routing problem, let $LF$ be the LP relaxation of formulation $F$ and $RF(\beta,\lambda,\mu)$ the relaxation obtained by relaxing the covering and fleet constraints (2)–(4) with penalties $\lambda \in \mathbb{R}^{N_C}$, $\mu \in \mathbb{R}_-^{N_S+1}$ and marginal costs $\beta$ solving (12). Then:
--
--   1. for every instance and route families for which $LF$ is feasible, some admissible $(\beta,\lambda,\mu)$ satisfies
--   $$z(RF(\beta,\lambda,\mu)) \ge z(LF),$$
--   so that $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)) \ge z(LF)$;
--   2. there are an instance, route families and an admissible $(\beta,\lambda,\mu)$ with $RF$ feasible and $z(RF(\beta,\lambda,\mu)) > z(LF)$.
--
--   The theorem justifies using the Lagrangean relaxation $RF$ (and its further relaxation $\overline{RF}$) as the lower-bounding device of the exact method instead of the LP relaxation.
--
--   **Formalization Note.** Part 1 assumes $LF$ feasible: when $LF$ is infeasible, $z(LF) = +\infty$ and the supremum over penalties need not be attained. Part 2 additionally requires $RF$ to be feasible, ruling out a gap caused only by $z(RF) = +\infty$. Route families are arbitrary finite families of elementary routes with costs computed along closed walks.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 301, Theorem 2

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LPCompare_Relaxations

namespace TwoEchelonCVRP.LPCompare

/-- **Theorem 2 (Baldacci et al. 2013, p. 301).** "The relation
`max_{β,λ,μ} {z(RF(β, λ, μ))} ⩾ z(LF)` holds, and such inequality can be strict."
(1) Whenever `LF` is feasible, some admissible `(β, λ, μ, μ₀)` attains `z(RF(β, λ, μ)) ≥ z(LF)`.
(2) There are an instance, a route system and an admissible `(β, λ, μ, μ₀)` with `RF` feasible
and `z(LF) < z(RF(β, λ, μ))`. -/
theorem theorem_2 :
    (∀ (I : Instance) (RS : RouteSystem I), (∃ p : LFPoint RS, IsFeasibleLF p) →
      ∃ (beta : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ),
        Admissible RS beta lam mu mu0 ∧ zLF RS ≤ zRF RS beta lam mu mu0) ∧
    (∃ (I : Instance) (RS : RouteSystem I) (beta : Fin I.nc → Fin I.ns → ℝ)
      (lam : Fin I.nc → ℝ) (mu : Fin I.ns → ℝ) (mu0 : ℝ),
      Admissible RS beta lam mu mu0 ∧ zLF RS < zRF RS beta lam mu mu0 ∧
        zRF RS beta lam mu mu0 < ⊤) := by sorry

end TwoEchelonCVRP.LPCompare
