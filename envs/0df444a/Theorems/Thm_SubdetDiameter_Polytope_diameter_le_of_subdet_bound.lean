-- Prove2me | Theorems.Thm_SubdetDiameter_Polytope_diameter_le_of_subdet_bound
-- name    : SubdetDiameter.Polytope.diameter_le_of_subdet_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:08:13.086978+00:00
-- url     : https://prove2.me/theorems/c3dc54a7-9e47-40d6-92cd-78e329aa519a
-- title:
--   Theorem 2: the diameter of an integral polytope is $O(\Delta^2 n^{3.5}\log n\Delta)$
-- statement:
--   Let $A \in \mathbb{Z}^{m\times n}$ be an integer matrix all of whose sub-determinants (of every order, including the entries) are bounded by $\Delta$ in absolute value, let $b \in \mathbb{R}^m$, and suppose $P = \{x \in \mathbb{R}^n : Ax \le b\}$ is bounded, i.e. a polytope. Then any two vertices of $P$ are joined by a path of at most
--   $$2\,\Big\lfloor \sqrt{2\pi}\,\Delta^2\, n^{5/2}\,\ln\!\big(2^n\, n!\, n^{n/2}\,\Delta^n\big)\Big\rfloor + 2$$
--   edges in the vertex-edge graph of $P$; that is, the combinatorial diameter of $P$ is at most this number.
--
--   Since $\ln(2^n n!\, n^{n/2}\Delta^n) = O(n \log(n\Delta))$, the bound is $O(\Delta^2 n^{3.5}\log(n\Delta))$, and it does not depend on the number $m$ of inequalities. For totally unimodular $A$ ($\Delta = 1$) it gives $O(n^{3.5}\log n)$, improving the earlier bound of Dyer and Frieze.
--
--   **Formalization Note** The paper writes $O(\Delta^2 n^{3.5}\log n\Delta)$; the proof yields the explicit bound above: by Eq. (1) and $\mathrm{vol}(I_0) \ge 1/(n!\,n^{n/2}\Delta^n)$ (p. 106), the first breadth-first-search iteration $j^*$ whose discovered vertices cover more than half of the unit ball satisfies $j^* \le \lfloor K\rfloor + 1$ with $K = \sqrt{2\pi}\Delta^2 n^{5/2}\ln(2^n n!\,n^{n/2}\Delta^n)$, and the diameter is at most $2j^*$. The polytope is `Hirsch.Hpoly (rowVec A) b` and "diameter at most $B$" is `Hirsch.DiamLE P B` from the published `Hirsch_model`. No non-degeneracy, full-dimensionality or rank hypothesis is imposed: the paper removes non-degeneracy by perturbing $b$, and a bounded nonempty polyhedron is automatically pointed. For empty $P$ the statement is vacuous; $\mathrm{Real.log}\,0 = 0$ only arises when $\Delta = 0$, where a bounded $P$ is empty or $n = 0$.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 105, Theorem 2 (explicit constant from its proof, pp. 105–106: Eq. (1) and vol(I_0) ≥ 1/(n!·n^{n/2}Δ^n)); model p. 103

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_SubdetDiameter_Polytope_model

namespace SubdetDiameter.Polytope

theorem diameter_le_of_subdet_bound (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℝ) (Δ : ℕ) (hΔ : SubdetBound A Δ)
    (hbdd : Bornology.IsBounded (Hirsch.Hpoly (rowVec A) b)) :
    Hirsch.DiamLE (Hirsch.Hpoly (rowVec A) b)
      (2 * ⌊Real.sqrt (2 * Real.pi) * (Δ : ℝ) ^ 2 * (n : ℝ) ^ ((5 : ℝ) / 2) *
          Real.log (2 ^ n * (n.factorial : ℝ) * (n : ℝ) ^ ((n : ℝ) / 2) * (Δ : ℝ) ^ n)⌋₊
        + 2) := by sorry

end SubdetDiameter.Polytope
