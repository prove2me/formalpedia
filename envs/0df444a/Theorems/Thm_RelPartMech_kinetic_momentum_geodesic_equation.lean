-- Prove2me | Theorems.Thm_RelPartMech_kinetic_momentum_geodesic_equation
-- name    : RelPartMech.kinetic_momentum_geodesic_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T23:14:04.109262+00:00
-- url     : https://prove2.me/theorems/b8c10506-4013-409d-a1c5-511a71efe215
-- title:
--   Hamiltonian mechanics recovers the geodesic equation with the force tensor
-- statement:
--   Consider a charged particle in extended phase space with canonical coordinates $(q^\alpha,p_\alpha)$ on $\mathbb R^n\times\mathbb R^n$ and canonical Poisson bracket ($\{q^\alpha,p_\beta\}=\delta^\alpha_\beta$). Let $g_{\alpha\beta}(x)$ be a smooth, symmetric, nondegenerate metric with Christoffel symbols $\Gamma^\gamma_{\delta\alpha}$, $A_\alpha(x)$ a smooth vector potential with force tensor $F_{\alpha\beta}=\partial_\alpha A_\beta-\partial_\beta A_\alpha$, $e$ the charge and $m\neq0$ the mass. With kinetic momentum $\Pi_\alpha=p_\alpha-eA_\alpha(x)$ and Hamiltonian
--
--   $$
--   H=\frac1{2m}\,\Pi_\alpha g^{\alpha\beta}\Pi_\beta ,
--   $$
--
--   write $d_s f=\{f,H\}$ for the evolution along the affine parameter $s$. Then
--
--   $$
--   D_s\Pi_\alpha \;=\; d_s\Pi_\alpha - d_s x^\delta\,\Gamma^\gamma_{\delta\alpha}\,\Pi_\gamma \;=\; \frac{e}{m}\,F_{\alpha\beta}\,g^{\beta\gamma}\,\Pi_\gamma .
--   $$
--
--   This is the geodesic equation modified by the force tensor (the covariant Lorentz-force law), recovered purely from Hamiltonian particle mechanics, where the metric enters only as the linear relation between kinetic momentum and velocity.
--
--   **Formalization Note** Everything is expressed in a single global chart; $d_s$ is the canonical Poisson bracket with $H$, evaluated at an arbitrary phase-space point $(x,p)$. The charge, written $q$ in the source, is called $e$.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 4, eq. (9), final line (D_s Π_α = (q/m) F_αβ g^βγ Π_γ)

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem kinetic_momentum_geodesic_equation {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (A : CovectorField n) (hA : ∀ α, ContDiff ℝ ∞ (A α)) (e m : ℝ) (hm : m ≠ 0)
    (α : Fin n) (x p : Coord n) :
    poisson (kineticMomentum A e α) (hamiltonian g A e m) x p
      - ∑ δ, ∑ γ, poisson (posFn δ) (hamiltonian g A e m) x p * christoffel g γ δ α x
          * kineticMomentum A e γ x p =
      (e / m) * ∑ β, ∑ γ, forceTensor A α β x * ginv g x β γ * kineticMomentum A e γ x p := by
  sorry

end RelPartMech
