-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_lemma_3_11
-- name    : SwitchOptStop.Boundary.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:28.108536+00:00
-- url     : https://prove2.me/theorems/9834a8df-7d1f-4f26-a547-6eb4e5843aa4
-- title:
--   Lemma 3.11, p. 13 — smooth fit: V(ι, ·) ∈ C¹((0, ∞)²)
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. For each regime $\iota$,
--   $$
--   V(\iota,\cdot)\in\mathscr C^1\big((0,\infty)^2\big).
--   $$
--
--   This is the principle of smooth fit across the optimal stopping boundary.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 13, Lemma 3.11

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Lemma 3.11 (p. 13), smooth fit: `V(ι, ·) ∈ C¹((0, ∞)²)`. -/
theorem lemma_3_11 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    ∀ ι : Fin 2, ContDiffOn ℝ 1 (value m S ι) openQuadrant := by sorry

end SwitchOptStop.Boundary
