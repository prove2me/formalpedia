-- Prove2me | Theorems.Thm_ThomsonProblem_N7_slab_s93_90
-- name    : ThomsonProblem.N7.slab_s93_90
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-09T23:56:08.649736+00:00
-- url     : https://prove2.me/theorems/b08f92d0-e95c-4cca-93f5-b6d152a99452
-- title:
--   Thomson $N=7$, slab 5: minimal pair with $t_{01}\in[-\tfrac{93}{100},-\tfrac{9}{10}]$ gives $E>E(P)$
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
--   2. $-\tfrac{93}{100}\ \le\ t_{01}\ \le\ -\tfrac{9}{10}$.
--
--   Then
--
--   $$E(P)\ <\ E(y).$$
--
--   This is slab 5 of the five slabs that, together with the cap $t_{01}\le-\tfrac{99}{100}$ and Case 1 (all $t_{ij}\ge-\tfrac9{10}$), cover all configurations in the proof of the Thomson problem for seven electrons. The hypothesis that the pair $(0,1)$ minimises the inner products is the *minimal-pair normal form*: every admissible configuration can be relabelled into it, and relabelling does not change the energy. In the source each slab is handled by its own typed three-point certificate with margin about $2.6\cdot10^{-6}$.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin 3)` and the energy, admissibility and $P$ are the shared definitions `coulombEnergy`, `IsAdmissible` and `pentagonalBipyramid` of `Def_ThomsonProblem_defs`; the inner product is written `inner ℝ (y i) (y j)`.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package (snapshot 2026-09-27), https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §6.5 (table, slab 5 `s93_90`) and §7.1 'Slabs'; Lean `ThomsonN7.Final.slab_s93_90` (https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L17826) with `ThomsonN7.Glue.slabSpec_sound` (https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L12750)

import Definitions.Def_ThomsonProblem_defs

namespace ThomsonProblem

theorem N7.slab_s93_90 : ∀ y : Fin 7 → Space, IsAdmissible y → (-93 / 100 : ℝ) ≤ inner ℝ (y 0) (y 1) →
    inner ℝ (y 0) (y 1) ≤ -9 / 10 → (∀ i j, i ≠ j → inner ℝ (y 0) (y 1) ≤ inner ℝ (y i) (y j)) →
    coulombEnergy pentagonalBipyramid < coulombEnergy y := by sorry

end ThomsonProblem
