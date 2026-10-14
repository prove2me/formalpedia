-- Prove2me | Theorems.Thm_Plasticity_Aux_window_avg_three_point
-- name    : Plasticity.Aux.window_avg_three_point
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:17.47215+00:00
-- url     : https://prove2.me/theorems/adb942ec-e765-43bd-b293-76fa1d4d3fb5
-- title:
--   Window averaging cancels first-order terms: the three-point planar form
-- statement:
--   Let $g\colon\mathbb R^2\to\mathbb R$ satisfy
--   $$|g(s,r)-g(s',r')|\le|s-s'|+|r-r'|\qquad(s,r,s',r'\in\mathbb R),$$
--   let $h>0$, $t\ge0$, and let $K$ be a real number such that
--   $$K\le g(s-t,r)+g(s,r-t)+g(s+t,r+t)-3g(s,r)\qquad\text{for all } s,r\in[-h,h].$$
--   Then
--   $$K\le\frac{3t^2}{h}.$$
--
--   The three displacements $(-t,0)$, $(0,-t)$, $(t,t)$ sum to zero, so averaging over the square $[-h,h]^2$ cancels all first-order terms; the remaining second-order terms are $(t^2+t^2+(2t)^2)/(2h)$. It is the scalar step of the additivity estimate in the sphere-preservation theorem.
--
--   **Formalization Note** $g$ is written as a curried function of two real variables.
-- source:
--   This repository: expositions/sphere_preservation_general.md §3, estimates (10)–(12), with h=1/16 there

import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

namespace Plasticity.Aux
theorem window_avg_three_point (g : ℝ → ℝ → ℝ)
    (hg : ∀ s r s' r' : ℝ, |g s r - g s' r'| ≤ |s - s'| + |r - r'|) (h t K : ℝ)
    (hh : 0 < h) (ht : 0 ≤ t)
    (hK : ∀ s ∈ Set.Icc (-h) h, ∀ r ∈ Set.Icc (-h) h,
      K ≤ g (s - t) r + g s (r - t) + g (s + t) (r + t) - 3 * g s r) :
    K ≤ 3 * t ^ 2 / h := by sorry
end Plasticity.Aux
