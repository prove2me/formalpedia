-- Prove2me | Theorems.Thm_ThomsonN7_Reg_energy_ge_cubic
-- name    : ThomsonN7.Reg.energy_ge_cubic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T02:07:30.022237+00:00
-- url     : https://prove2.me/theorems/0f13a5a7-1d7f-4220-a397-0df193cd9074
-- title:
--   Thomson $N=7$: cubic lower bound for the energy excess over the pentagonal bipyramid
-- statement:
--   Let $P=(P_0,\dots,P_6)$ be the pentagonal bipyramid with the regular pentagon $P_k=(\cos\tfrac{2\pi k}5,\sin\tfrac{2\pi k}5,0)$ at indices $k=0,\dots,4$ and the poles $(0,0,\pm1)$ at indices $5,6$; let $\varphi(t)=(2-2t)^{-1/2}$, so that $\|x-y\|^{-1}=\varphi(\langle x,y\rangle)$ for unit vectors, and write $g_{ij}=\langle P_i,P_j\rangle$ and $E(y)=\sum_{i<j}\|y_i-y_j\|^{-1}$. Let $W_{ij}=\varphi(g_{ij})^3$ for $i\ne j$, $W_{ii}=0$, and $\mu_i=\sum_j W_{ij}g_{ij}$.
--
--   Let $y=(y_0,\dots,y_6)$ be seven pairwise distinct unit vectors in $\mathbb R^3$, write $h_i=y_i-P_i$ and $\tau_{ij}=\langle y_i,y_j\rangle-g_{ij}$. Then
--
--   $$\tfrac12\sum_{i,j}W_{ij}\langle h_i,h_j\rangle-\tfrac12\sum_i\mu_i\|h_i\|^2+\sum_{i<j}\Big(\tfrac32\varphi(g_{ij})^5\tau_{ij}^2+\tfrac52\varphi(g_{ij})^7\tau_{ij}^3\Big)\ \le\ E(y)-E(P).$$
--
--   It follows from the pairwise Taylor/Bregman bound $\varphi(g+\tau)\ge\varphi(g)+\varphi'(g)\tau+\tfrac12\varphi''(g)\tau^2+\tfrac16\varphi'''(g)\tau^3$ on $[-1,1)$ together with the first-order (equilibrium) identity of $P$, which rewrites the linear terms as the $W$/$\mu$ quadratic form.
--
--   **Formalization Note** All named objects (`pentBipyramid`, `coulombEnergy`, `Base.phi`, `Reg.W`, `Reg.muP`, `Reg.gP`, `Reg.tau`, `Reg.Dpair`, `Reg.Qhess`, `Reg.Pen`, `Glue.TubeRigid`) come from the platform definition `ThomsonN7_core`, taken verbatim from the source; `R3` is `EuclideanSpace ℝ (Fin 3)`.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package, https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §7.2 step 5 (local minimality); Lean `ThomsonN7.Reg.energy_ge_cubic`, https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L6703

import Definitions.Def_ThomsonN7_core

namespace ThomsonN7

theorem Reg.energy_ge_cubic {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1) (hinj : Function.Injective y) :
    1 / 2 * ∑ i, ∑ j, Reg.W i j * inner ℝ (y i - pentBipyramid i) (y j - pentBipyramid j)
      - 1 / 2 * ∑ i, Reg.muP i * ‖y i - pentBipyramid i‖ ^ 2
      + ∑ i, ∑ j ∈ Finset.Ioi i, (3 / 2 * Base.phi (Reg.gP i j) ^ 5 * Reg.tau y i j ^ 2
          + 5 / 2 * Base.phi (Reg.gP i j) ^ 7 * Reg.tau y i j ^ 3)
      ≤ coulombEnergy y - coulombEnergy pentBipyramid := by sorry

end ThomsonN7
