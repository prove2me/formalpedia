-- Prove2me | Theorems.Thm_RelPartMech_velocity_geodesic_equation
-- name    : RelPartMech.velocity_geodesic_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:11:38.166305+00:00
-- url     : https://prove2.me/theorems/ac952a4d-3c4e-4a4c-8178-67be63d367cf
-- title:
--   Geodesic equation with force in position–velocity form
-- statement:
--   Let $H=\frac12 m\,u^\alpha g_{\alpha\beta}u^\beta=\frac1{2m}\Pi_\alpha g^{\alpha\beta}\Pi_\beta$ with $u^\alpha=\frac1m g^{\alpha\beta}\Pi_\beta$, $\Pi_\alpha=p_\alpha-eA_\alpha$, smooth $g$ and $A$, and $m\neq0$. Write $d_s f=\{f,H\}$. Then
--
--   $$
--   D_s u^\alpha \;=\; d_s u^\alpha + u^\beta\, d_s x^\gamma\, \Gamma^\alpha_{\beta\gamma} \;=\; \frac{e}{m}\,F^{\alpha\gamma}g_{\gamma\beta}\,u^\beta .
--   $$
--
--   This is the geodesic equation modified by the Lorentz force, now in position–velocity variables.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 7, eq. (14), last line

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem velocity_geodesic_equation {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α : Fin n) (x p : Coord n) :
    poisson (velocity g A e m α) (hamiltonian g A e m) x p
      + ∑ β, ∑ γ, velocity g A e m β x p * poisson (posFn γ) (hamiltonian g A e m) x p
          * christoffel g α β γ x =
      (e / m) * ∑ γ, ∑ β, forceTensorUp g A α γ x * g x γ β * velocity g A e m β x p := by
  sorry

end RelPartMech
