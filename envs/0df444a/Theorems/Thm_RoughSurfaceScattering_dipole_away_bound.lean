-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_away_bound
-- name    : RoughSurfaceScattering.dipole_away_bound
-- status  : Proved
-- author  : @もち
-- created : 2026-11-27T02:48:58.0318+00:00
-- url     : https://prove2.me/theorems/061d57f4-33bb-46b0-a1aa-22e65caf3f68
-- title:
--   Dipoles are uniformly $H^1$-bounded away from their poles
-- statement:
--   Let $k>0$, let $D_0$ be bounded and open, $x_0,\nu\in\mathbb R^2$ and $\delta>0$. Then
--   $$\sup_{z\in\bar B_\delta(x_0)}\big\|\nabla_x\Phi_k(\cdot,z)\cdot\nu\big\|_{H^1(D_0\setminus\bar B_{3\delta/2}(x_0))}<\infty.$$
--   On $D_0\setminus\bar B_{3\delta/2}(x_0)$ we have $\delta/2\le|x-z|\le R$. The first and second derivatives of $\Phi_k$ are continuous on the compact set $\{\delta/2\le|w|\le R\}$, so they are bounded uniformly, and $|D_0|<\infty$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, case Γ1 ≠ Γ2 with μ1 = 1 (hypersingular sources), PDF pp. 22-24 (∇Φ_k(·,x_j)·n is smooth away from x_0, uniformly in j).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_away_bound (k : ℝ) (hk : 0 < k) (D0 : Set R2) (hD : IsOpen D0)
    (hb : Bornology.IsBounded D0) (x0 ν : R2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ z ∈ Metric.closedBall x0 δ,
      h1Norm (D0 \ Metric.closedBall x0 (3 * δ / 2)) (dipoleSource k z ν) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
