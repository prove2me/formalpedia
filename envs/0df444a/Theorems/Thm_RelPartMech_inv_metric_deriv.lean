-- Prove2me | Theorems.Thm_RelPartMech_inv_metric_deriv
-- name    : RelPartMech.inv_metric_deriv
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:05:33.725368+00:00
-- url     : https://prove2.me/theorems/ce48682e-15e2-44ef-88c4-0debbc6ed406
-- title:
--   Derivative of the inverse metric
-- statement:
--   Let $g_{\alpha\beta}(x)$ be a smooth, symmetric, nondegenerate metric on a coordinate chart $\mathbb R^n$, with inverse $g^{\alpha\beta}(x)$. Then for all indices $\alpha,\beta,\gamma$ and every point $x$,
--
--   $$
--   \partial_\alpha g^{\beta\gamma} = -\,g^{\beta\delta}\,g^{\gamma\epsilon}\,\partial_\alpha g_{\delta\epsilon},
--   $$
--
--   with summation over $\delta,\epsilon$. It follows from differentiating $g^{\beta\delta}g_{\delta\gamma}=\delta^\beta_\gamma$.
--
--   This identity is used throughout the note to trade derivatives of the inverse metric for derivatives of the metric.
--
--   **Formalization Note** Space-time is a single global chart $\mathbb R^n$ (`Fin n → ℝ`); $\partial_\alpha$ is the Fréchet derivative in direction $e_\alpha$; the metric is assumed smooth, symmetric and pointwise invertible (`IsSmoothMetric`), with no signature condition.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 1, eq. (2), second and third lines

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem inv_metric_deriv {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (α β γ : Fin n) (x : Coord n) :
    pd α (fun y => ginv g y β γ) x =
      -∑ δ, ∑ ε, ginv g x β δ * ginv g x γ ε * pd α (fun y => g y δ ε) x := by sorry

end RelPartMech
