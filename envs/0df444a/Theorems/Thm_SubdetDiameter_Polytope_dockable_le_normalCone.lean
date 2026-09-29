-- Prove2me | Theorems.Thm_SubdetDiameter_Polytope_dockable_le_normalCone
-- name    : SubdetDiameter.Polytope.dockable_le_normalCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:04:42.416246+00:00
-- url     : https://prove2.me/theorems/c1a264f7-c86e-4257-a892-f213a00b392e
-- title:
--   Lemma 3: $D(S_v)/\mathrm{vol}(S_v) \le \Delta^2 n^3$ for the normal cones of a polytope
-- statement:
--   Let $A \in \mathbb{Z}^{m\times n}$ have all sub-determinants bounded by $\Delta$ in absolute value, and let $P = \{x \in \mathbb{R}^n : Ax \le b\}$ be a polytope (a bounded polyhedron) that is non-degenerate, i.e. every vertex has exactly $n$ tight inequalities. For a vertex $v$ of $P$ let $C_v$ be its normal cone and $S_v = C_v \cap B_n$ the corresponding spherical cone, with $B_n$ the closed unit ball. Then the dockable surface $D(S_v)$ (the $(n-1)$-dimensional measure of the part of $\partial S_v$ inside the open unit ball) satisfies
--   $$D(S_v) \le \Delta^2 n^3 \cdot \mathrm{vol}(S_v).$$
--
--   This is inequality (4) of the paper: the upper half of the volume-expansion argument, bounding how much surface a single normal cone can offer relative to its volume. It is where integrality of $A$ and the sub-determinant bound enter.
--
--   **Formalization Note** The paper writes the ratio $D(S_v)/\mathrm{vol}(S_v) \le \Delta^2 n^3$; the Lean statement is the equivalent multiplicative form in $[0,\infty]$ ($S_v$ is full-dimensional, so its volume is positive and finite). Non-degeneracy is the paper's standing assumption of §1.1 (p. 104, "we can assume"), used here because the proof needs $C_v$ to be simplicial; boundedness is §2's standing assumption "$P$ is a polytope". $D$ is `μHE[n-1]` of `frontier S_v ∩ ball 0 1`.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 108, Lemma 3 (= inequality (4), p. 107); standing assumptions p. 104 (non-degenerate) and p. 106 (P is a polytope)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_SubdetDiameter_Polytope_model
import Definitions.Def_SubdetDiameter_Polytope_sphericalCone

namespace SubdetDiameter.Polytope

theorem dockable_le_normalCone (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℝ) (Δ : ℕ) (hΔ : SubdetBound A Δ)
    (hbdd : Bornology.IsBounded (Hirsch.Hpoly (rowVec A) b))
    (hnd : NonDegenerate A b)
    (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly (rowVec A) b)) :
    dockable (FirstOrderOpt.ConvexTheory.normalCone (Hirsch.Hpoly (rowVec A) b) v ∩
        Metric.closedBall 0 1) ≤
      ((Δ : ENNReal) ^ 2 * (n : ENNReal) ^ 3) *
        MeasureTheory.volume (FirstOrderOpt.ConvexTheory.normalCone
          (Hirsch.Hpoly (rowVec A) b) v ∩ Metric.closedBall 0 1) := by sorry

end SubdetDiameter.Polytope
