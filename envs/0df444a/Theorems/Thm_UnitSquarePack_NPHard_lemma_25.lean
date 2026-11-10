-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_lemma_25
-- name    : UnitSquarePack.NPHard.lemma_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:21:06.205641+00:00
-- url     : https://prove2.me/theorems/5f25af2a-9629-4dcf-86fe-2134cf3cd03e
-- title:
--   Lemma 25 — a vertical stack crossing a horizontal stack
-- statement:
--   Let $S \subseteq \mathbb Z^2$ be the lower-left corners of a packing of $2\times 2$ squares with integer coordinates (pairwise disjoint interiors). For $x, y \in \mathbb Z$ write $\langle x, y\rangle$ for the square of the packing covering the reference center $[2x-1, 2x] \times [2y-1, 2y]$ (upper right corner $(2x, 2y)$). A square **pushes up** (down, left, right) if that reference center lies in one of its lower (upper, right, left) quadrants. Let $x_0, y_0 \in \mathbb N$ and suppose every reference center with $0 \le x \le x_0+1$, $0 \le y \le y_0 + 1$ is covered by a square of the packing, and
--
--   - $\langle 1, 0\rangle, \dots, \langle x_0, 0\rangle$ push up (a vertical stack), and
--   - $\langle 0, 1\rangle, \dots, \langle 0, y_0\rangle$ push right (a horizontal stack).
--
--   **Lemma 25.** Then
--
--   1. $\langle 1, y_0+1\rangle, \dots, \langle x_0, y_0+1\rangle$ push up,
--   2. $\langle x_0+1, 1\rangle, \dots, \langle x_0+1, y_0\rangle$ push right,
--   3. $\langle x_0+1, y_0+1\rangle$ pushes up or right, and
--   4. $\langle 0, y_0+1\rangle$ pushes up or $\langle x_0+1, 0\rangle$ pushes right.
--
--   So when a vertical stack crosses a horizontal stack where the reference centers form the regular grid, the two stacks together grow in width by at least two squares; this is the source of the crossing variables $x(a,b) \in \{0,1,2\}$ in the clause-component inequalities (3)–(6).
--
--
--   The printed statement does not explicitly exclude an empty initial list. The formal statement retains zero widths; INSIGHTS I5 records a counterexample to conclusions 3 and 4 at x₀ = 0, y₀ = 1. No positivity correction is inserted into the mission item.
--
--   Differences from the source:
--   - reading: a packing of 2 × 2 squares where each of these reference centers is covered → a family of integer-coordinate 2 × 2 squares with pairwise disjoint interiors, with no container polygon; reason: pushing is defined (p. 6) only for squares of a perfect packing, which have integer coordinates; the lemma names no polygon
--   - encoding: ⟨x, y⟩ pushes up (down, left, right) → some square of the packing covering [2x−1,2x]×[2y−1,2y] has it inside one of its lower (upper, right, left) quadrants; reason: the covering square is unique in a packing, so 'some' and 'the' agree
--   - reading: In conclusion, … the two stacks together grow in width by at least 2 squares → not a separate clause; the four items 1–4 are stated; reason: the closing sentence restates items 1–4 in terms of stack widths, which the lemma does not define
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 24, Lemma 25 (pp. 24–25)

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_ReferenceCenters

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Lemma 25: a vertical stack `⟨1, 0⟩, …, ⟨x₀, 0⟩` pushing up crossing a horizontal stack
`⟨0, 1⟩, …, ⟨0, y₀⟩` pushing right, in a packing of integer `2 × 2` squares covering every
reference center `⟨x, y⟩`, `0 ≤ x ≤ x₀ + 1`, `0 ≤ y ≤ y₀ + 1`. -/
theorem lemma_25 (S : Set (ℤ × ℤ)) (hS : IsIntPacking S) (x₀ y₀ : ℕ)
    (hcov : ∀ x y : ℤ, 0 ≤ x → x ≤ x₀ + 1 → 0 ≤ y → y ≤ y₀ + 1 → Covers S x y)
    (hup : ∀ x : ℤ, 1 ≤ x → x ≤ x₀ → RefPushesUp S x 0)
    (hright : ∀ y : ℤ, 1 ≤ y → y ≤ y₀ → RefPushesRight S 0 y) :
    (∀ x : ℤ, 1 ≤ x → x ≤ x₀ → RefPushesUp S x (y₀ + 1)) ∧
    (∀ y : ℤ, 1 ≤ y → y ≤ y₀ → RefPushesRight S (x₀ + 1) y) ∧
    (RefPushesUp S (x₀ + 1) (y₀ + 1) ∨ RefPushesRight S (x₀ + 1) (y₀ + 1)) ∧
    (RefPushesUp S 0 (y₀ + 1) ∨ RefPushesRight S (x₀ + 1) 0) := by sorry

end UnitSquarePack.NPHard
