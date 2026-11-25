-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_contDiffOn
-- name    : RoughSurfaceScattering.dipole_contDiffOn
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T00:31:52.62194+00:00
-- url     : https://prove2.me/theorems/b9d1f8bc-4510-422d-9d3f-a4b7dea97f48
-- title:
--   The dipole $\nabla_x\Phi_k(x,z)\cdot\nu$ is $C^1$ away from $z$
-- statement:
--   For $k\ge0$ and $z,\nu\in\mathbb R^2$, the function $x\mapsto\nabla_x\Phi_k(x,z)\cdot\nu$ is $C^1$ on $\{x\ne z\}$. Equivalently, $\Phi_k(\cdot,z)$ is $C^2$ off $z$. This follows from $\Phi_k=a_k\Phi_0+b_k$, with $a_k,b_k$ given by entire power series in $|x-z|^2$ and $\Phi_0=\frac1{2\pi}\ln\frac1{|x-z|}$ smooth off $z$.
--
--   **Formalization Note** The dipole is the platform's `dipoleSource`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3 and its proof, PDF pp. 21-22; smoothness of Φ_k off the diagonal (Section 2, p. 4).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_contDiffOn (k : ℝ) (hk : 0 ≤ k) (z ν : R2) :
    ContDiffOn ℝ 1 (dipoleSource k z ν) {x | x ≠ z} := by sorry

end RoughSurfaceScattering
