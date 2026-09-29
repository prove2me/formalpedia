-- Prove2me | Theorems.Thm_SubdetDiameter_Polytope_bfs_iteration_bound
-- name    : SubdetDiameter.Polytope.bfs_iteration_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:07:42.458986+00:00
-- url     : https://prove2.me/theorems/d6a9caa6-c836-46a9-a0ef-8150f1e718d2
-- title:
--   Eq. (1): breadth-first search covers half the ball within $\sqrt{2\pi}\,\Delta^2 n^{2.5}\ln(2^n/\mathrm{vol}(I_0))$ iterations
-- statement:
--   Let $A \in \mathbb{Z}^{m\times n}$ have all sub-determinants bounded by $\Delta$ in absolute value and let $P = \{x \in \mathbb{R}^n : Ax \le b\}$ be a non-degenerate polytope. Start breadth-first search in the polyhedral graph $G_P$ at a vertex $v$, and let $I_j$ be the set of vertices discovered during the first $j$ iterations (so $I_0 = \{v\}$, and $I_j$ is the set of vertices at graph distance at most $j$ from $v$). Write $\mathrm{vol}(U) = \mathrm{vol}\big(\bigcup_{u\in U} C_u \cap B_n\big)$. If
--   $$\mathrm{vol}(I_j) \le \tfrac12\,\mathrm{vol}(B_n),$$
--   then
--   $$j \le \sqrt{2\pi}\,\Delta^2 n^{2.5}\cdot \ln\big(2^n/\mathrm{vol}(I_0)\big).$$
--
--   This is the iteration count in the proof of the paper's main theorem: combined with a lower bound on $\mathrm{vol}(I_0)$ it bounds the number of breadth-first-search rounds before the discovered vertices cover more than half of the ball, and twice that number bounds the diameter.
--
--   **Formalization Note** Non-degeneracy is the paper's §1.1 assumption (p. 104) under which the proof of Theorem 2 is carried out. $\mathrm{vol}(I_0)$ is converted to a real number; it is finite because $I_0$'s cone is intersected with the unit ball (and positive, since the normal cone of a vertex of a non-degenerate polytope is full-dimensional). $I_j$ is `layer P v j`, the endpoints of $j$-step walks from $v$ with stationary steps allowed.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 105, proof of Theorem 2, Eq. (1)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SubdetDiameter_Polytope_model

namespace SubdetDiameter.Polytope

theorem bfs_iteration_bound (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℝ) (Δ : ℕ) (hΔ : SubdetBound A Δ)
    (hbdd : Bornology.IsBounded (Hirsch.Hpoly (rowVec A) b))
    (hnd : NonDegenerate A b)
    (v : EuclideanSpace ℝ (Fin n))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly (rowVec A) b)) (j : ℕ)
    (hj : vertexVol (Hirsch.Hpoly (rowVec A) b) (layer (Hirsch.Hpoly (rowVec A) b) v j) ≤
      (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    (j : ℝ) ≤ Real.sqrt (2 * Real.pi) * (Δ : ℝ) ^ 2 * (n : ℝ) ^ ((5 : ℝ) / 2) *
      Real.log (2 ^ n /
        (vertexVol (Hirsch.Hpoly (rowVec A) b) (layer (Hirsch.Hpoly (rowVec A) b) v 0)).toReal) := by sorry

end SubdetDiameter.Polytope
