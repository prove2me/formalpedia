-- Prove2me | Theorems.Thm_Plasticity_Aux_window_avg_two_point
-- name    : Plasticity.Aux.window_avg_two_point
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:17.810816+00:00
-- url     : https://prove2.me/theorems/7617c44e-b92b-4749-87ea-b5fe6a598e31
-- title:
--   Window averaging cancels first-order terms: the two-point form
-- statement:
--   Let $g\colon\mathbb R\to\mathbb R$ be $1$-Lipschitz, let $h>0$ and $t,u\ge0$, and let $K$ be a real number such that
--   $$K\le u\,g(s-t)+t\,g(s+u)-(t+u)\,g(s)\qquad\text{for all } s\in[-h,h].$$
--   Then
--   $$K\le\frac{ut^2+tu^2}{2h}.$$
--
--   The right side of the hypothesis is a weighted second difference of $g$ whose first-order terms cancel because $u\cdot(-t)+t\cdot u=0$; averaging over the window $[-h,h]$ replaces $g$ by a function with $(1/h)$-Lipschitz derivative, which turns the cancellation into a quadratic bound. It is the scalar step of the mixed-scale estimate in the sphere-preservation theorem.
-- source:
--   This repository: expositions/sphere_preservation_general.md §2, estimates (5)–(6) and the averaging step after (6), with h=1/8 there

import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.Basic

namespace Plasticity.Aux
theorem window_avg_two_point (g : ℝ → ℝ) (hg : LipschitzWith 1 g) (h t u K : ℝ)
    (hh : 0 < h) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hK : ∀ s ∈ Set.Icc (-h) h, K ≤ u * g (s - t) + t * g (s + u) - (t + u) * g s) :
    K ≤ (u * t ^ 2 + t * u ^ 2) / (2 * h) := by sorry
end Plasticity.Aux
