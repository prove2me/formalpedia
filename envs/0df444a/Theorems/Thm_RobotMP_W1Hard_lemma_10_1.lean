-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_10_1
-- name    : RobotMP.W1Hard.lemma_10_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:41.947316+00:00
-- url     : https://prove2.me/theorems/c2298713-cf22-41cd-8533-63f82a8ef802
-- title:
--   Lemma 10.1 — a square of side 2 meets the reference centers in area exactly 1
-- statement:
--   Let $Q = [a, a+2] \times [b, b+2]$ be a closed axis-aligned square of side length $2$ at an arbitrary real position $(a, b) \in \mathbb R^2$, and let $C = \bigcup_{(u,v) \in \mathbb Z^2} [2u, 2u+1] \times [2v, 2v+1]$ be the union of the reference centers. Then
--   $$\operatorname{area}(Q \cap C) = 1.$$
--
--   This area count is what forces a packing with as many squares as reference centers to cover every reference center.
--
--   Differences from the source:
--   - encoding: a unit square placed by its centre → square2 (a, b) = [a, a+2] × [b, b+2] given by its lower-left corner, from the published UnitSquarePack_NPHard_Squares; reason: same squares, shifted parameter.
--   - encoding: area → Lebesgue measure on ℝ × ℝ (value in [0, ∞]); reason: Lean convention.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 56, Lemma 10.1

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_Squares
import Definitions.Def_RobotMP_W1Hard_ReferenceCenters

set_option autoImplicit false

namespace RobotMP.W1Hard

/-- Lemma 10.1: every closed axis-aligned square of side 2, at any real position, meets the
union of the reference centers in a set of area exactly 1. -/
theorem lemma_10_1 (c : ℝ × ℝ) :
    MeasureTheory.volume (UnitSquarePack.NPHard.square2 c ∩ refCenters) = 1 := by sorry

end RobotMP.W1Hard
