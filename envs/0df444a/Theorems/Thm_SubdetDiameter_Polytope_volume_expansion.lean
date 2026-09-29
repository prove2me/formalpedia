-- Prove2me | Theorems.Thm_SubdetDiameter_Polytope_volume_expansion
-- name    : SubdetDiameter.Polytope.volume_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:07:08.077975+00:00
-- url     : https://prove2.me/theorems/c2b2d11f-2f62-4ede-9bec-fb65d24f49a0
-- title:
--   Lemma 1: volume expansion $\mathrm{vol}(\mathcal N(I)) \ge \sqrt{2/\pi}\,\mathrm{vol}(I)/(\Delta^2 n^{2.5})$
-- statement:
--   Let $A \in \mathbb{Z}^{m\times n}$ have all sub-determinants bounded by $\Delta$ in absolute value, and let $P = \{x \in \mathbb{R}^n : Ax \le b\}$ be a non-degenerate polytope (bounded, every vertex with exactly $n$ tight inequalities). Let $V$ be the vertex set of the polyhedral graph $G_P$, and for $U \subseteq V$ let $\mathrm{vol}(U) = \mathrm{vol}\big(\bigcup_{v\in U} C_v \cap B_n\big)$ be the volume of the union of the normal cones of $U$ inside the unit ball. If $I \subseteq V$ satisfies $\mathrm{vol}(I) \le \tfrac12\,\mathrm{vol}(B_n)$, then the neighbourhood $\mathcal N(I)$ — the vertices outside $I$ adjacent to some vertex of $I$ — satisfies
--   $$\mathrm{vol}(\mathcal N(I)) \ge \sqrt{\frac{2}{\pi}}\,\frac{1}{\Delta^2 n^{2.5}}\cdot \mathrm{vol}(I).$$
--
--   Volume expansion is the engine of the paper's diameter bound: each breadth-first-search step multiplies the covered volume by $1 + \sqrt{2/\pi}/(\Delta^2 n^{2.5})$ until half of the ball is covered.
--
--   **Formalization Note** Non-degeneracy is added as a hypothesis: the paper assumes it without loss of generality for the whole of §1.1–§2 (p. 104, "We can assume that $P$ is non-degenerate"), and the proof uses it through Lemma 3. $\mathcal N(I)$ excludes $I$ itself; with $I$ included the inequality would be trivial, since the constant is below $1$. Adjacency is `Hirsch.Adj`. When $\Delta = 0$ or $n = 0$ Lean's division by zero makes the constant $0$ and the statement trivial; for a nonempty polytope with $n \ge 1$ one has $\Delta \ge 1$.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 105, Lemma 1 (= inequality (2), p. 106); non-degeneracy assumption p. 104

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SubdetDiameter_Polytope_model

namespace SubdetDiameter.Polytope

theorem volume_expansion (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℝ) (Δ : ℕ) (hΔ : SubdetBound A Δ)
    (hbdd : Bornology.IsBounded (Hirsch.Hpoly (rowVec A) b))
    (hnd : NonDegenerate A b)
    (I : Set (EuclideanSpace ℝ (Fin n)))
    (hI : I ⊆ Set.extremePoints ℝ (Hirsch.Hpoly (rowVec A) b))
    (hvol : vertexVol (Hirsch.Hpoly (rowVec A) b) I ≤
      (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    ENNReal.ofReal (Real.sqrt (2 / Real.pi) / ((Δ : ℝ) ^ 2 * (n : ℝ) ^ ((5 : ℝ) / 2))) *
        vertexVol (Hirsch.Hpoly (rowVec A) b) I ≤
      vertexVol (Hirsch.Hpoly (rowVec A) b) (nbhd (Hirsch.Hpoly (rowVec A) b) I) := by sorry

end SubdetDiameter.Polytope
