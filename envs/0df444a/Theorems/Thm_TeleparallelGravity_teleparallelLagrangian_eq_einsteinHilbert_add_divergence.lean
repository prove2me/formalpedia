-- Prove2me | Theorems.Thm_TeleparallelGravity_teleparallelLagrangian_eq_einsteinHilbert_add_divergence
-- name    : TeleparallelGravity.teleparallelLagrangian_eq_einsteinHilbert_add_divergence
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T22:44:49.736686+00:00
-- url     : https://prove2.me/theorems/14dfae0e-4a9f-4faa-a517-eb06d01d690f
-- title:
--   Teleparallel Lagrangian = Einstein-Hilbert Lagrangian + divergence (Section 2, after Eq. (14))
-- statement:
--   Let $h^a{}_\mu$ be a smooth tetrad on $\mathbb R^4$ with $h=\det(h^a{}_\mu)>0$ everywhere, and let $c,G$ be real constants. Then at every point
--   $$\frac{c^4h}{16\pi G}S^{\rho\mu\nu}T_{\rho\mu\nu}=-\frac{c^4}{16\pi G}\sqrt{-g}\,\mathring R+\partial_\mu\Big(-\frac{c^4}{8\pi G}\,h\,T^{\nu\mu}{}_\nu\Big),$$
--   i.e. the teleparallel Lagrangian (10) equals the Einstein-Hilbert Lagrangian up to an explicit total divergence. Here $g=\det g_{\mu\nu}$, $\mathring R$ is the scalar curvature of the Christoffel connection (with $R^\rho{}_{\theta\mu\nu}=\partial_\mu\mathring\Gamma^\rho{}_{\theta\nu}-\cdots$, $\mathring R_{\theta\nu}=\mathring R^\rho{}_{\theta\rho\nu}$), and $T^{\nu\mu}{}_\nu=g^{\mu\beta}T^\nu{}_{\beta\nu}$. The paper states the equivalence only "up to a divergence"; the divergence term is made explicit here.
-- source:
--   R. Aldrovandi, J. G. Pereira, K. H. Vu, "Selected Topics in Teleparallel Gravity", Brazilian Journal of Physics 34 (2004), no. 4A, 1374-1380, https://doi.org/10.1590/S0103-97332004000700009 — Teleparallel Lagrangian = Einstein-Hilbert Lagrangian + divergence (Section 2, after Eq. (14))

import Mathlib
import Definitions.Def_TeleparallelGravity_Defs

open scoped ContDiff

namespace TeleparallelGravity
theorem teleparallelLagrangian_eq_einsteinHilbert_add_divergence
    (c G : ℝ) (h : TetradField) (hh : IsTetrad h) (hpos : ∀ x, 0 < tetradDet h x)
    (x : Spacetime) :
    teleparallelLagrangian c G h x =
      einsteinHilbertLagrangian c G h x +
        ∑ μ, pd μ (fun y => -(c ^ 4 / (8 * Real.pi * G)) *
          (tetradDet h y * torsionVectorUp h μ y)) x := by
  sorry
end TeleparallelGravity
