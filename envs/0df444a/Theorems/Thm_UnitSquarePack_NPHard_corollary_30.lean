-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_corollary_30
-- name    : UnitSquarePack.NPHard.corollary_30
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:20:59.952419+00:00
-- url     : https://prove2.me/theorems/25f40970-d0b4-48fe-8e2d-88c3dcd60b1e
-- title:
--   Corollary 30 — between a left and a right static row, all but k up-pushing blocks grow by one square
-- statement:
--   In a perfect integer packing of an orthogonally convex grid polygon P, use the reference centers of Lemma 23, allowing shifted intermediate rows. Rows 0 and k+1 have regular reference centers. Every square of row 0 pushes left and every square of row k+1 pushes right.
--
--   Let [a_i,b_i], i ∈ Fin j, be nonempty pairwise disjoint blocks of lower-row indices. All squares ⟨x,0⟩ in these blocks push up. All upper-row squares named below exist.
--
--   **Corollary 30.** For all but at most k indices i, every square ⟨x,k+1⟩ with a_i−1 ≤ x ≤ b_i pushes up:
--
--   $$\#\{i : \neg\forall x\in[a_i-1,b_i],\ \langle x,k+1\rangle\text{ pushes up}\}\le k.$$
--
--   The case k=0 is the static-shift growth in Lemma 24. The blocks are separate blocks of squares, not a list of overlapping subintervals of one block.
--
--   Differences from the source:
--   - generalization: left and right static rows forced by polygon edges → all squares in the two rows push left and right, respectively; reason: every static row has these directions (p. 24); the boundary mechanism forcing them is not needed
--   - reading: the two static rows and the rows between them in §4.6 → a perfect packing in the orthogonally convex grid polygon, regular reference centers at rows 0 and k+1, possibly shifted intermediate rows; reason: static rows have regular centers (p. 24); the shifted lower variable row is explicitly present in §4.6
--   - reading: blocks of squares ⟨a_i,0⟩ through ⟨b_i,0⟩ → nonempty pairwise disjoint index intervals; reason: blocks denote separate groups of squares (Figure 45); counting arbitrary overlapping subintervals would count one loss repeatedly
--   - encoding: the squares ⟨a_i−1,k+1⟩ through ⟨b_i,k+1⟩ → htop asserts that each named square exists; reason: the square notation presupposes coverage of its reference center; no common clipping interval is imposed on the other rows
--   - encoding: perfect packing and for all but k indices → coverage of all reference centers and Set.ncard of the failing indices in Fin j; reason: coverage is equivalent to the cardinality definition by Lemma 23 and boundedness; Fin j is finite
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 36, Corollary 30

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_ReferenceCenters

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Corollary 30 in the perfect-packing setting of §4.6. The two static rows have
regular centers; intermediate rows may be shifted. The blocks are pairwise disjoint.
All the squares named in the upper row exist. -/
theorem corollary_30 (vs : List (ℤ × ℤ)) (hP : IsGridPolygon vs)
    (hconv : IsOrthogonallyConvex (region vs)) (I : Set ℤ) (S : Set (ℤ × ℤ))
    (hpack : IsPerfectIntPacking (region vs) I S) (k : ℕ)
    (hregular : (0 : ℤ) ∈ I ∧ (k : ℤ) + 1 ∈ I)
    (hleft : ∀ x : ℤ, Covers S x 0 → RefPushesLeft S x 0)
    (hright : ∀ x : ℤ, Covers S x (k + 1) → RefPushesRight S x (k + 1))
    (j : ℕ) (a b : Fin j → ℤ) (hab : ∀ i, a i ≤ b i)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a i') (b i')))
    (hblock : ∀ i, ∀ x : ℤ, a i ≤ x → x ≤ b i → RefPushesUp S x 0)
    (htop : ∀ i, ∀ x : ℤ, a i - 1 ≤ x → x ≤ b i → Covers S x (k + 1)) :
    {i : Fin j | ¬ ∀ x : ℤ, a i - 1 ≤ x → x ≤ b i → RefPushesUp S x (k + 1)}.ncard ≤ k := by sorry

end UnitSquarePack.NPHard
