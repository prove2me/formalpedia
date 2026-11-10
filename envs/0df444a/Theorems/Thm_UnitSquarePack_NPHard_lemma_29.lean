-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_lemma_29
-- name    : UnitSquarePack.NPHard.lemma_29
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:20:52.348532+00:00
-- url     : https://prove2.me/theorems/3717bf4c-3de1-4999-bfdc-600b25d448bf
-- title:
--   Lemma 29 — at most k up-pushes are lost between two rows with k rows between them
-- statement:
--   Work in the perfect-packing setting of §4.6: P is an orthogonally convex grid polygon and S is a packing of integer-coordinate 2×2 squares contained in P that covers every reference center. The reference cells in row y are [2x−1,2x]×[2y−1,2y] when y ∈ I, and [2x,2x+1]×[2y−1,2y] otherwise, as in Lemma 23. In particular, intermediate rows need not have the same horizontal reference alignment.
--
--   Fix an integer row y₁ and k ∈ ℕ. Let L be all up-pushing squares in row y₁, and U be the squares in row y₁+k+1 whose left x-coordinate equals x_s−1, x_s, or x_s+1 for some s ∈ L, where x_s is the left x-coordinate of s.
--
--   **Lemma 29.** At most k squares of U push down. This is the full bound on losses between the two rows, including the shifted lower variable row named in the opening of §4.6.
--
--   Differences from the source:
--   - reading: two rows of squares with k rows between them in §4.6 → all squares of rows y₁ and y₁+k+1 in a perfect integer packing of an orthogonally convex grid polygon, with reference-row set I; reason: §4 inherits the polygon and perfect-packing setting; §4.3 permits shifted rows and §4.6 explicitly names the shifted lower variable row
--   - encoding: perfect packing has as many squares as reference centers → every square is contained in P and every reference center of P is covered; reason: Lemma 23 gives one reference center per square; disjoint interiors give at most one covering square per center; the bounded polygon makes both sets finite
--   - encoding: at most k squares in U push down → Set.ncard of U intersected with the down-pushing row squares is at most k; reason: the polygon is bounded and corners are integral, so S and U are finite; all coordinate differences are in ℤ
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 35, Lemma 29

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_ReferenceCenters

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Lemma 29, in the perfect-packing setting of §4.6, including the shifted reference
rows of §4.3. The two rows are `y₁` and `y₁ + k + 1`. At most `k` squares of the upper
row whose left coordinate is within one of an up-pushing lower square push down. -/
theorem lemma_29 (vs : List (ℤ × ℤ)) (hP : IsGridPolygon vs)
    (hconv : IsOrthogonallyConvex (region vs)) (I : Set ℤ) (S : Set (ℤ × ℤ))
    (hpack : IsPerfectIntPacking (region vs) I S) (y₁ : ℤ) (k : ℕ) :
    let L := upRowSquares S I y₁
    let U := {u | u ∈ rowSquaresFor S I (y₁ + k + 1) ∧
      ∃ s ∈ L, u.1 = s.1 - 1 ∨ u.1 = s.1 ∨ u.1 = s.1 + 1}
    (U ∩ downRowSquares S I (y₁ + k + 1)).ncard ≤ k := by sorry

end UnitSquarePack.NPHard
