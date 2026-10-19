-- Prove2me | Theorems.Thm_RelPartMech_metric_hessian_of_gSymbol_zero
-- name    : RelPartMech.metric_hessian_of_gSymbol_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T23:12:56.632293+00:00
-- url     : https://prove2.me/theorems/4b36e306-f2cd-401e-975a-8f3040ebaf85
-- title:
--   If $G\equiv0$ then the metric is a Hessian
-- statement:
--   Let $g$ be a smooth metric on the coordinate space $\mathbb R^n$ such that $G_{\alpha\beta\gamma}=\partial_\alpha g_{\beta\gamma}-\partial_\beta g_{\alpha\gamma}$ vanishes identically. Then there is a smooth scalar function $S$ with
--
--   $$
--   g_{\alpha\beta} = \partial_\alpha\partial_\beta S .
--   $$
--
--   **Formalization Note** The source argues locally; here the chart is all of $\mathbb R^n$, on which closed one-forms are exact.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), p. 9, eq. (16)

import Mathlib
import Definitions.Def_RelPartMech_coordinates

open scoped ContDiff

namespace RelPartMech

theorem metric_hessian_of_gSymbol_zero {n : ℕ} (g : MetricField n) (hg : IsSmoothMetric g)
    (hG : ∀ α β γ x, gSymbol g α β γ x = 0) :
    ∃ S : Coord n → ℝ, ContDiff ℝ ∞ S ∧ ∀ α β x, g x α β = pd α (pd β S) x := by sorry

end RelPartMech
