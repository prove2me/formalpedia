-- Prove2me | Theorems.Thm_RobotMP_W1Hard_lemma_10_2
-- name    : RobotMP.W1Hard.lemma_10_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:42:43.272192+00:00
-- url     : https://prove2.me/theorems/cbfe01e4-d21e-4c7c-ba34-0ac583d6099e
-- title:
--   Lemma 10.2 — packing k squares in P with k reference centers covers each center by a single square
-- statement:
--   Let $P \subseteq \mathbb R^2$ be closed, cutting no reference center (each reference center lies inside $P$ or is disjoint from it), and containing exactly $k$ reference centers. Let $Q_0, \dots, Q_{k-1}$ be closed axis-aligned squares of side length $2$ contained in $P$ with pairwise disjoint interiors. Then every reference center $C \subseteq P$ satisfies
--   $$C \subseteq Q_i \quad\text{for some } i.$$
--
--   With this lemma the configurations of the reduction's polygon are read off as positions of squares over reference centers.
--
--   Differences from the source:
--   - generalization: P, the polygon constructed in §10 → any closed P that cuts no reference center and contains exactly k of them; reason: the polygon of §10 is closed and cuts no reference center (p. 56), so it is an instance.
--   - reading: "each reference center" → each reference center contained in P; reason: centers outside P are disjoint from P and from every square, and the paper counts the centers in P.
--   - encoding: squares by centre, "pack" → square2 by lower-left corner and the published IsPackingIn (squares inside P, pairwise disjoint interiors); reason: same packings, shifted parameter.
--   - encoding: "k is the number of reference centers in P" → the extended cardinality encard of the set of centers in P equals k; reason: excludes an infinite set being counted as 0.
-- source:
--   Agarwal, Holmgren, Stade, Near-Optimal Makespan and Parameterized Hardness for Multi-Robot Motion Planning, STOC 2027 submission (manuscript sha256 17b4fe59…), p. 56, Lemma 10.2

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_Squares
import Definitions.Def_RobotMP_W1Hard_ReferenceCenters

set_option autoImplicit false

namespace RobotMP.W1Hard

/-- Lemma 10.2: let `P` be closed, cutting no reference center and containing exactly `k`
reference centers. In every packing of `k` squares of side 2 in `P`, each reference center in
`P` is contained entirely in a single square. -/
theorem lemma_10_2 (P : Set (ℝ × ℝ)) (k : ℕ) (c : Fin k → ℝ × ℝ) (hP : IsClosed P)
    (hcut : CutsNoRefCenter P) (hk : (refCentersIn P).encard = k)
    (hpack : UnitSquarePack.NPHard.IsPackingIn P c) :
    ∀ ab ∈ refCentersIn P, ∃ i : Fin k, refCenter ab ⊆ UnitSquarePack.NPHard.square2 (c i) := by sorry

end RobotMP.W1Hard
