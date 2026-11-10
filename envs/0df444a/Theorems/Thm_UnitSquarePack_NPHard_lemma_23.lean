-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_lemma_23
-- name    : UnitSquarePack.NPHard.lemma_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:20:49.489053+00:00
-- url     : https://prove2.me/theorems/c6fa5aff-a7a0-49cb-b3f6-6693fb8e7bbc
-- title:
--   Lemma 23 — every integer 2×2 square contains exactly one reference center
-- statement:
--   Fix a set $P \subseteq \mathbb R^2$ and a set of rows $I \subseteq \mathbb Z$. The **reference centers** are the unit squares contained in $P$ of the form $[2k-1, 2k] \times [2\ell-1, 2\ell]$ with $\ell \in I$, or $[2k, 2k+1] \times [2\ell-1, 2\ell]$ with $\ell \notin I$ ($k, \ell \in \mathbb Z$).
--
--   **Lemma 23.** Every $2 \times 2$ square $[a, a+2] \times [b, b+2] \subseteq P$ with $a, b \in \mathbb Z$ contains exactly one reference center:
--   $$\exists!\, R:\ R \text{ is a reference center of } P \text{ for } I \ \text{ and } \ R \subseteq [a, a+2] \times [b, b+2].$$
--
--   With $I = \mathbb Z$ this is Lemma 7: in a packing with integer coordinates every square covers exactly one reference center, so a packing has at most as many squares as there are reference centers, and a **perfect** packing is one with exactly as many. The rows outside $I$ are the shifted rows needed by the variable components of §4.
--
--   Differences from the source:
--   - generalization: P is a grid polygon → P is any subset of ℝ²; reason: the statement never uses the shape of P (a reference center inside the square lies in P because the square does); grid polygons are a special case
--   - reading: I ⊂ ℤ → any I ⊆ ℤ, I = ℤ allowed; reason: Lemma 23 generalizes Lemma 7 (p. 23), which is the case I = ℤ
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 23, Lemma 23

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_GridPolygon
import Definitions.Def_UnitSquarePack_NPHard_Squares
import Definitions.Def_UnitSquarePack_NPHard_ReferenceCenters

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Lemma 23: with reference centers `[2k-1, 2k] × [2ℓ-1, 2ℓ]` (`ℓ ∈ I`) and
`[2k, 2k+1] × [2ℓ-1, 2ℓ]` (`ℓ ∉ I`) contained in `P`, every `2 × 2` square in `P` with integer
coordinates contains exactly one reference center. -/
theorem lemma_23 (P : Set (ℝ × ℝ)) (I : Set ℤ) (a b : ℤ)
    (h : square2 (toPlane (a, b)) ⊆ P) :
    ∃! R : Set (ℝ × ℝ), IsReferenceCenter P I R ∧ R ⊆ square2 (toPlane (a, b)) := by sorry

end UnitSquarePack.NPHard
