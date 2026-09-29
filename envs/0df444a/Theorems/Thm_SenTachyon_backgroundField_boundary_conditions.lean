-- Prove2me | Theorems.Thm_SenTachyon_backgroundField_boundary_conditions
-- name    : SenTachyon.backgroundField_boundary_conditions
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:03:30.406217+00:00
-- url     : https://prove2.me/theorems/eb4bc6d0-32e4-4cda-992c-ab2aa6188889
-- title:
--   Eqs. (5)–(6): boundary conditions of the background field
-- statement:
--   Let $\tilde R_1,\tilde R_2>0$ and let $A$ be the background field (4). With the transition functions $\Omega_1=\exp(ix^2\sigma_3/\tilde R_2)$ and $\Omega_2=1$ of (6), and the gauge transform $(\Omega\circ A)_\mu=\Omega A_\mu\Omega^{-1}-i(\partial_\mu\Omega)\Omega^{-1}$, the field satisfies, for $\mu=1,2$ and all $x^1,x^2$,
--   $$A_\mu(2\pi\tilde R_1,x^2)=(\Omega_1\circ A)_\mu(0,x^2),\qquad A_\mu(x^1,2\pi\tilde R_2)=(\Omega_2\circ A)_\mu(x^1,0).$$
--
--   These are the twisted periodicity conditions that make $A$ a gauge field on the dual torus carrying $\pm1$ unit of flux.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 2, eqs. (4)–(6)

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem backgroundField_boundary_conditions (R₁t R₂t : ℝ) (h₁ : 0 < R₁t) (h₂ : 0 < R₂t) :
    ∀ (μ : Fin 2) (x₁ x₂ : ℝ),
      backgroundField R₁t R₂t μ (2 * Real.pi * R₁t, x₂)
          = gaugeTransform (omega1 R₂t) (backgroundField R₁t R₂t) μ (0, x₂) ∧
      backgroundField R₁t R₂t μ (x₁, 2 * Real.pi * R₂t)
          = gaugeTransform omega2 (backgroundField R₁t R₂t) μ (x₁, 0) := by sorry
end SenTachyon
