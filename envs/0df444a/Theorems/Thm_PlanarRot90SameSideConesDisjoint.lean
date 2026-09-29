-- Prove2me | Theorems.Thm_PlanarRot90SameSideConesDisjoint
-- name    : PlanarRot90SameSideConesDisjoint
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T00:51:37.224395+00:00
-- url     : https://prove2.me/theorems/4b49510c-4deb-47f7-91b3-683e8ffee85a
-- title:
--   Narrow same-side quarter-turn cones are disjoint
-- statement:
--   Let $u$ and $d$ be nonzero planar directions, with $d$ not a positive scalar multiple of $u$. There is a constant $\kappa>0$ for which the two narrow quarter-turn cones
--
--   $$
--   a u+bR_{90}(u)\quad	ext{and}\quad c d+rR_{90}(d)$$
--
--   cannot meet when $a,c>0$, both transverse coefficients satisfy the relative bounds $|b|<\kappa a$ and $|r|<\kappa c$, and $br>0$. The result gives disjointness for the two cones lying on the same signed side of successive polygonal directions.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90SameSideConesDisjoint.lean#L1-L47

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

theorem PlanarRot90SameSideConesDisjoint {u d : EuclideanSpace ℝ (Fin 2)}
    (hu : u ≠ 0) (_hd : d ≠ 0)
    (hnot : ¬ ∃ A : ℝ, 0 < A ∧ d = A • u) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
        |b| < κ * a → |r| < κ * c →
          a • u + b • PlanarRot90 u ≠ c • d + r • PlanarRot90 d := by sorry
