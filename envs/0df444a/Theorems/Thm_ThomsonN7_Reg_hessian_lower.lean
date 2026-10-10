-- Prove2me | Theorems.Thm_ThomsonN7_Reg_hessian_lower
-- name    : ThomsonN7.Reg.hessian_lower
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T02:08:15.115586+00:00
-- url     : https://prove2.me/theorems/f809e0ef-dc77-407b-93c0-8e73c930cc16
-- title:
--   Thomson $N=7$: the penalised Hessian of the energy at the pentagonal bipyramid is positive definite
-- statement:
--   Let $P=(P_0,\dots,P_6)$ be the pentagonal bipyramid with the regular pentagon $P_k=(\cos\tfrac{2\pi k}5,\sin\tfrac{2\pi k}5,0)$ at indices $k=0,\dots,4$ and the poles $(0,0,\pm1)$ at indices $5,6$; let $\varphi(t)=(2-2t)^{-1/2}$, so that $\|x-y\|^{-1}=\varphi(\langle x,y\rangle)$ for unit vectors, and write $g_{ij}=\langle P_i,P_j\rangle$ and $E(y)=\sum_{i<j}\|y_i-y_j\|^{-1}$. Let $W_{ij}=\varphi(g_{ij})^3$ for $i\ne j$, $W_{ii}=0$, and $\mu_i=\sum_j W_{ij}g_{ij}$.
--
--   For $h=(h_0,\dots,h_6)\in(\mathbb R^3)^7$ define the quadratic form
--
--   $$Q(h)=\tfrac12\sum_{i,j}W_{ij}\langle h_i,h_j\rangle-\tfrac12\sum_i\mu_i\|h_i\|^2+\sum_{i<j}\tfrac32\varphi(g_{ij})^5\big(\langle P_i,h_j\rangle+\langle h_i,P_j\rangle\big)^2$$
--
--   and the penalty
--
--   $$\mathrm{Pen}(h)=\sum_i\langle P_i,h_i\rangle^2+G_{01}(h)^2+G_{02}(h)^2+G_{12}(h)^2,\qquad G_{ab}(h)=\sum_i\big(P_{i,a}h_{i,b}-P_{i,b}h_{i,a}\big).$$
--
--   Then for every $h$,
--
--   $$\frac{449}{100000}\sum_i\|h_i\|^2\ \le\ Q(h)+2\,\mathrm{Pen}(h).$$
--
--   This is the second-order (Hessian) half of the exact local minimality of the bipyramid: the penalty removes the normal directions and the three rotation directions, and on the complement the Hessian is uniformly positive. In the source it is proved by an exact sum-of-squares decomposition over interval enclosures of the trigonometric atoms.
--
--   **Formalization Note** All named objects (`pentBipyramid`, `coulombEnergy`, `Base.phi`, `Reg.W`, `Reg.muP`, `Reg.gP`, `Reg.tau`, `Reg.Dpair`, `Reg.Qhess`, `Reg.Pen`, `Glue.TubeRigid`) come from the platform definition `ThomsonN7_core`, taken verbatim from the source; `R3` is `EuclideanSpace ℝ (Fin 3)`.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package, https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §7.2 step 5 (local minimality); Lean `ThomsonN7.Reg.hessian_lower`, https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L9009

import Definitions.Def_ThomsonN7_core

namespace ThomsonN7

theorem Reg.hessian_lower (h : Fin 7 → R3) :
    449 / 100000 * ∑ i, ‖h i‖ ^ 2 ≤ Reg.Qhess h + 2 * Reg.Pen h := by sorry

end ThomsonN7
