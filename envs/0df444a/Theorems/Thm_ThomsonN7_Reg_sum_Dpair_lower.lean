-- Prove2me | Theorems.Thm_ThomsonN7_Reg_sum_Dpair_lower
-- name    : ThomsonN7.Reg.sum_Dpair_lower
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T02:08:02.941166+00:00
-- url     : https://prove2.me/theorems/d17248eb-f74b-4e44-a373-46b7204d7a1d
-- title:
--   Thomson $N=7$: the cubic remainders near the pentagonal bipyramid are $O(r)\sum\|y_i-P_i\|^2$
-- statement:
--   Let $P=(P_0,\dots,P_6)$ be the pentagonal bipyramid with the regular pentagon $P_k=(\cos\tfrac{2\pi k}5,\sin\tfrac{2\pi k}5,0)$ at indices $k=0,\dots,4$ and the poles $(0,0,\pm1)$ at indices $5,6$; let $\varphi(t)=(2-2t)^{-1/2}$, so that $\|x-y\|^{-1}=\varphi(\langle x,y\rangle)$ for unit vectors, and write $g_{ij}=\langle P_i,P_j\rangle$ and $E(y)=\sum_{i<j}\|y_i-y_j\|^{-1}$.
--
--   For $y\in(\mathbb R^3)^7$ write $h_i=y_i-P_i$, $\tau_{ij}=\langle y_i,y_j\rangle-g_{ij}$ and
--
--   $$D_{ij}(y)=\tfrac32\varphi(g_{ij})^5\tau_{ij}^2+\tfrac52\varphi(g_{ij})^7\tau_{ij}^3-\tfrac32\varphi(g_{ij})^5\big(\langle P_i,h_j\rangle+\langle h_i,P_j\rangle\big)^2.$$
--
--   If $0\le r\le\tfrac1{1000}$ and $\|h_i\|\le r$ for all $i$ (no unit-norm assumption), then
--
--   $$-28\,r\sum_i\|h_i\|^2\ \le\ \sum_{i<j}D_{ij}(y).$$
--
--   Since $\tau_{ij}=\langle P_i,h_j\rangle+\langle h_i,P_j\rangle+\langle h_i,h_j\rangle$, each $D_{ij}$ consists of terms of order at least three in $h$, and the bound makes this quantitative on the $r$-ball.
--
--   **Formalization Note** All named objects (`pentBipyramid`, `coulombEnergy`, `Base.phi`, `Reg.W`, `Reg.muP`, `Reg.gP`, `Reg.tau`, `Reg.Dpair`, `Reg.Qhess`, `Reg.Pen`, `Glue.TubeRigid`) come from the platform definition `ThomsonN7_core`, taken verbatim from the source; `R3` is `EuclideanSpace ℝ (Fin 3)`.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package, https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §7.2 step 5 (local minimality); Lean `ThomsonN7.Reg.sum_Dpair_lower`, https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L8949

import Definitions.Def_ThomsonN7_core

namespace ThomsonN7

theorem Reg.sum_Dpair_lower {y : Fin 7 → R3} {r : ℝ} (hr : r ≤ 1 / 1000)
    (hρ : ∀ i, ‖y i - pentBipyramid i‖ ≤ r) :
    -(28 * r * ∑ i, ‖y i - pentBipyramid i‖ ^ 2)
      ≤ ∑ i, ∑ j ∈ Finset.Ioi i, Reg.Dpair y i j := by sorry

end ThomsonN7
