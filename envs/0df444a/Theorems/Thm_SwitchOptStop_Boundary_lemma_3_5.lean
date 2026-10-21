-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_lemma_3_5
-- name    : SwitchOptStop.Boundary.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:39.361186+00:00
-- url     : https://prove2.me/theorems/4d771720-65ad-464e-a8da-df10b9102f13
-- title:
--   Lemma 3.5, p. 10 — V(ι, ·) and V^N(ι, ·) are increasing, concave and continuous on (0, ∞)²
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. For each regime $\iota$, the value function $V(\iota,\cdot)$ is increasing (in the coordinatewise order), concave and continuous on $(0,\infty)^2$; the same holds for $V^N(\iota,\cdot)$ for every $N>0$.
--
--   Monotonicity and concavity of $V$ are what make the stopping region a region above a decreasing convex boundary curve.
--
--   **Formalization Note** "Increasing" is `MonotoneOn` for the product order on $\mathbb R^2$.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 10, Lemma 3.5

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Lemma 3.5 (p. 10): `V(ι, ·)` is increasing, concave and continuous on `(0, ∞)²`, and so is
`V^N(ι, ·)` for every `N > 0`. -/
theorem lemma_3_5 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    ∀ ι : Fin 2,
      (MonotoneOn (value m S ι) openQuadrant ∧ ConcaveOn ℝ openQuadrant (value m S ι) ∧
        ContinuousOn (value m S ι) openQuadrant) ∧
      ∀ N : ℝ, 0 < N →
        MonotoneOn (valueN m S N ι) openQuadrant ∧ ConcaveOn ℝ openQuadrant (valueN m S N ι) ∧
          ContinuousOn (valueN m S N ι) openQuadrant := by sorry

end SwitchOptStop.Boundary
