-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_helmholtz
-- name    : RoughSurfaceScattering.dipole_helmholtz
-- status  : Proved
-- author  : @もち
-- created : 2026-11-27T02:48:59.646055+00:00
-- url     : https://prove2.me/theorems/283004bc-ef5b-4a20-82df-57b85c95b2c7
-- title:
--   The dipole $\nabla_x\Phi_k(\cdot,z)\cdot\nu$ solves the Helmholtz equation
-- statement:
--   For $k\ge0$ and $z,\nu\in\mathbb R^2$, the function $x\mapsto\nabla_x\Phi_k(x,z)\cdot\nu$ satisfies $\Delta w+k^2w=0$ on $\mathbb R^2\setminus\{z\}$.
--   $\Phi_k(\cdot,z)$ is smooth off $z$ and solves the Helmholtz equation there. Directional derivatives commute with $\Delta$ for smooth functions, so $\Delta\partial_\nu\Phi_k+k^2\partial_\nu\Phi_k=\partial_\nu(\Delta\Phi_k+k^2\Phi_k)=0$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, case Γ1 ≠ Γ2 with μ1 = 1 (hypersingular sources), PDF pp. 22-24 (incident hypersingular point sources, Theorem 5.3).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_helmholtz (k : ℝ) (hk : 0 ≤ k) (z ν : R2) :
    IsHelmholtzOn {x | x ≠ z} k (dipoleSource k z ν) := by sorry

end RoughSurfaceScattering
