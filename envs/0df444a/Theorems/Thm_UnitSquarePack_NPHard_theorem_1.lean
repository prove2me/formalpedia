-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_theorem_1
-- name    : UnitSquarePack.NPHard.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:20:58.57274+00:00
-- url     : https://prove2.me/theorems/6d0c5144-1efa-499e-9c66-57f64712f7cb
-- title:
--   Theorem 1 — 2×2 square packing is NP-hard for orthogonally convex grid polygons
-- statement:
--   **2 × 2-Square-Packing** asks, given a polygon $P$ and an integer $k$, whether $P$ has room for $k$ axis-aligned squares of size $2 \times 2$: closed squares $[a, a+2] \times [b, b+2]$ with arbitrary real $a, b$, each contained in $P$, with pairwise disjoint interiors. A **grid polygon** is an orthogonal polygon with vertices at integer coordinates, given by the binary coordinates of its vertices; it is **orthogonally convex** if its intersection with every horizontal and every vertical line is connected (such a polygon is simple). The language `orthoConvexSquarePacking` consists of the binary codes of the pairs (vertex list, $k$) where the vertex list is a grid polygon whose closed region $P$ is orthogonally convex and has room for $k$ squares.
--
--   **Theorem 1.** The problem 2 × 2-Square-Packing is NP-hard, even for orthogonally convex grid polygons:
--   $$\forall L \in \mathrm{NP}:\quad L \le_p \texttt{orthoConvexSquarePacking}.$$
--
--   This answers, for $2\times 2$ squares and in a stronger form, Problem 56 of The Open Problems Project and the conjecture of Baur and Fekete (2001) that maximum packings of $s \times s$ squares in simple grid polygons can be found in polynomial time. NP-hardness of the version with holes has been known since 1981; for simple polygons it was open. NP-membership is not part of the theorem.
--
--   Differences from the source:
--   - encoding: a polygon P and an integer k; P given as the coordinates of its vertices in binary (p. 3) → a word over Bool: the vertex count, the vertices as sign-and-magnitude binary integers, then k ∈ ℕ in binary; the language holds exactly the codes of grid polygons whose closed region is orthogonally convex and has room for k squares; reason: the paper's standard representation; a negative k is a trivial yes-instance
--   - encoding: P has room for k axis-aligned 2 × 2 squares → k closed squares [a, a + 2] × [b, b + 2], a, b ∈ ℝ, each contained in the closed region (boundary curve and its bounded complementary components), pairwise disjoint interiors; reason: packing means without overlap; squares may touch each other and the boundary
--   - encoding: NP-hard → KingTerrain.NPHard.IsNPHard: every NP language over every finite nonempty alphabet is CookPvsNP.PolyReducible to the language; reason: the published notion of NP-hardness (polynomial-time Turing-machine many-one reductions)
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 1, Theorem 1 (proof §4.9, p. 54)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KingTerrain_NPHard_Complexity
import Definitions.Def_UnitSquarePack_NPHard_PackingLanguage

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Theorem 1: 2 × 2-Square-Packing is NP-hard, even for orthogonally convex grid polygons. -/
theorem theorem_1 : KingTerrain.NPHard.IsNPHard orthoConvexSquarePacking := by sorry

end UnitSquarePack.NPHard
