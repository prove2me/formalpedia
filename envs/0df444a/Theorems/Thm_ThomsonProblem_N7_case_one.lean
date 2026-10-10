-- Prove2me | Theorems.Thm_ThomsonProblem_N7_case_one
-- name    : ThomsonProblem.N7.case_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-09T23:55:48.329981+00:00
-- url     : https://prove2.me/theorems/53e719db-2c8c-4fda-8765-b994087f1963
-- title:
--   Thomson $N=7$, Case 1: no near-antipodal pair gives $E\ge E(P)+3\cdot10^{-4}$
-- statement:
--   Let $P=(P_0,\dots,P_6)$ be the pentagonal bipyramid of the mission (the poles $(0,0,\pm1)$ and the regular pentagon $(\cos\tfrac{2\pi k}{5},\sin\tfrac{2\pi k}{5},0)$, $k=0,\dots,4$), and for a configuration $y=(y_0,\dots,y_6)$ write
--
--   $$E(y)=\sum_{0\le i<j\le 6}\frac{1}{\|y_i-y_j\|}$$
--
--   for its Coulomb energy. A configuration is *admissible* if its seven points lie on the unit sphere $S^2\subset\mathbb R^3$ and are pairwise distinct. Write $t_{ij}=\langle y_i,y_j\rangle$ for the pairwise inner products.
--
--   If $y$ is admissible and all its pairwise inner products satisfy $t_{ij}\ge-\tfrac{9}{10}$ for $i\ne j$, then
--
--   $$E(y)\ \ge\ E(P)+\frac{3}{10^{4}}.$$
--
--   This is Case 1 of the proof of the Thomson problem for seven electrons: configurations without a near-antipodal pair have energy strictly above that of the pentagonal bipyramid, with an explicit margin. In the source it is obtained from a single degree-5 three-point semidefinite certificate together with a polynomial minorant of $t\mapsto(2-2t)^{-1/2}$.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin 3)` and the energy, admissibility and $P$ are the shared definitions `coulombEnergy`, `IsAdmissible` and `pentagonalBipyramid` of `Def_ThomsonProblem_defs`; the inner product is written `inner ℝ (y i) (y j)`.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package (snapshot 2026-09-27), https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §5 (Case 1: all inner products at least −9/10), §5.4 'Result'; Lean theorem `ThomsonN7.case1_margin`, https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L10495

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem N7.case_one : ∀ y : Fin 7 → Space, IsAdmissible y →
    (∀ i j, i ≠ j → (-9 / 10 : ℝ) ≤ inner ℝ (y i) (y j)) →
    coulombEnergy pentagonalBipyramid + 3 / 10000 ≤ coulombEnergy y := by sorry

end ThomsonProblem
