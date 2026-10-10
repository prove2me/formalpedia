-- Prove2me | Theorems.Thm_ThomsonProblem_N7_cap
-- name    : ThomsonProblem.N7.cap
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-09T23:55:59.969408+00:00
-- url     : https://prove2.me/theorems/b12f10c7-31d1-44a2-a85f-d73fa6d14829
-- title:
--   Thomson $N=7$, the cap: minimal pair with $t_{01}\le-0.99$ gives $E\ge E(P)$
-- statement:
--   Let $P=(P_0,\dots,P_6)$ be the pentagonal bipyramid of the mission (the poles $(0,0,\pm1)$ and the regular pentagon $(\cos\tfrac{2\pi k}{5},\sin\tfrac{2\pi k}{5},0)$, $k=0,\dots,4$), and for a configuration $y=(y_0,\dots,y_6)$ write
--
--   $$E(y)=\sum_{0\le i<j\le 6}\frac{1}{\|y_i-y_j\|}$$
--
--   for its Coulomb energy. A configuration is *admissible* if its seven points lie on the unit sphere $S^2\subset\mathbb R^3$ and are pairwise distinct. Write $t_{ij}=\langle y_i,y_j\rangle$ for the pairwise inner products.
--
--   Let $y$ be admissible and suppose that
--
--   1. the pair $(0,1)$ realises the smallest inner product: $t_{01}\le t_{ij}$ for all $i\ne j$;
--   2. this pair is nearly antipodal: $t_{01}\le-\tfrac{99}{100}$.
--
--   Then
--
--   $$E(P)\ \le\ E(y).$$
--
--   This is the *cap* cell of Case 2 of the proof of the Thomson problem for seven electrons; it is the only cell that contains the pentagonal bipyramid itself (whose poles have $t_{01}=-1$), so the bound is sharp here. The hypothesis that the pair $(0,1)$ minimises the inner products is the *minimal-pair normal form*: every admissible configuration can be relabelled into it, and relabelling does not change the energy. In the source it follows from a near-sharp typed three-point certificate combined with a rigidity argument and an exact second-order local minimality theorem for $P$.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin 3)` and the energy, admissibility and $P$ are the shared definitions `coulombEnergy`, `IsAdmissible` and `pentagonalBipyramid` of `Def_ThomsonProblem_defs`; the inner product is written `inner ℝ (y i) (y j)`.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package (snapshot 2026-09-27), https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §7.2 'The cap'; Lean `ThomsonN7.Final.capspec_cap` (https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L16169) with `ThomsonN7.Glue.capSpec_sound` (https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L12729), first component of the conclusion

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem N7.cap : ∀ y : Fin 7 → Space, IsAdmissible y → inner ℝ (y 0) (y 1) ≤ -99 / 100 →
    (∀ i j, i ≠ j → inner ℝ (y 0) (y 1) ≤ inner ℝ (y i) (y j)) →
    coulombEnergy pentagonalBipyramid ≤ coulombEnergy y := by sorry

end ThomsonProblem
