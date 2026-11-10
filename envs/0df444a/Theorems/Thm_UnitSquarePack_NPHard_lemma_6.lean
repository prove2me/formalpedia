-- Prove2me | Theorems.Thm_UnitSquarePack_NPHard_lemma_6
-- name    : UnitSquarePack.NPHard.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:19:58.176064+00:00
-- url     : https://prove2.me/theorems/d9c60c76-a27e-4f5e-b482-48593b7482b1
-- title:
--   Lemma 6 — integer-coordinate packings suffice
-- statement:
--   Let $P \subseteq \mathbb R^2$ be a finite union of closed unit grid cells $[i, i+1] \times [j, j+1]$, $(i,j) \in \mathbb Z^2$ — in particular the closed region of any grid polygon. Suppose $P$ contains $k$ axis-aligned squares $[a_r, a_r + 2] \times [b_r, b_r + 2]$ ($a_r, b_r \in \mathbb R$) with pairwise disjoint interiors.
--
--   **Lemma 6.** Then $P$ also contains $k$ such squares with pairwise disjoint interiors whose vertices all have integer coordinates:
--   $$\exists\, (a'_r, b'_r)_{r<k} \in (\mathbb Z^2)^k:\quad [a'_r, a'_r+2]\times[b'_r, b'_r+2] \subseteq P,\quad \operatorname{int}(\cdot)\ \text{pairwise disjoint}.$$
--
--   The lemma lets every later argument restrict to packings with integer coordinates, where each square contains exactly one reference center (Lemma 23) and has only four possible positions around it. The paper calls it folklore and refers to Baur and Fekete; its printed proof stops after choosing a minimizer (INSIGHTS I3).
--
--   Differences from the source:
--   - generalization: P is a grid polygon → P is any finite union of closed unit grid cells; reason: the closed region of every grid polygon, simple or with holes, is the union of the unit grid cells it contains, so the statement specializes to the paper's
--   - encoding: the coordinates of the vertices of all the squares are integers → every lower-left corner lies in ℤ² (then all four vertices are integer points); reason: a 2×2 square's vertices are its corner plus (0 or 2, 0 or 2)
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 6, Lemma 6

import Mathlib
import Definitions.Def_UnitSquarePack_NPHard_GridPolygon
import Definitions.Def_UnitSquarePack_NPHard_Squares

set_option autoImplicit false

namespace UnitSquarePack.NPHard

/-- Lemma 6: if a grid polygon (here: any finite union of closed unit grid cells) can be packed
with `k` axis-aligned `2 × 2` squares, then it can be packed with `k` such squares whose vertices
all have integer coordinates. -/
theorem lemma_6 (P : Set (ℝ × ℝ)) (hP : IsGridCellUnion P) (k : ℕ) (c : Fin k → ℝ × ℝ)
    (hc : IsPackingIn P c) :
    ∃ d : Fin k → ℤ × ℤ, IsPackingIn P (fun i => toPlane (d i)) := by sorry

end UnitSquarePack.NPHard
