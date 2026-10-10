-- Prove2me | Theorems.Thm_ThomsonN7_Glue_tubeRigid_of_le
-- name    : ThomsonN7.Glue.tubeRigid_of_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-10T02:07:35.378963+00:00
-- url     : https://prove2.me/theorems/a87ae6ac-e759-44ab-bb20-57ad5d40136e
-- title:
--   Thomson $N=7$: tube rigidity of the pentagonal bipyramid for $\tau\le 1/10$
-- statement:
--   Let $P=(P_0,\dots,P_6)$ be the pentagonal bipyramid with the regular pentagon $P_k=(\cos\tfrac{2\pi k}5,\sin\tfrac{2\pi k}5,0)$ at indices $k=0,\dots,4$ and the poles $(0,0,\pm1)$ at indices $5,6$; let $\varphi(t)=(2-2t)^{-1/2}$, so that $\|x-y\|^{-1}=\varphi(\langle x,y\rangle)$ for unit vectors, and write $g_{ij}=\langle P_i,P_j\rangle$ and $E(y)=\sum_{i<j}\|y_i-y_j\|^{-1}$. Let $c_1=\cos\tfrac{2\pi}5$ and $c_2=\cos\tfrac{4\pi}5$.
--
--   Let $\tau\le\tfrac1{10}$ and let $y_0,\dots,y_6$ be unit vectors in $\mathbb R^3$ such that
--
--   1. $|\langle y_0,y_1\rangle+1|\le\tau$;
--   2. $|\langle y_0,y_r\rangle|\le\tau$ and $|\langle y_1,y_r\rangle|\le\tau$ for $r=2,\dots,6$;
--   3. for $2\le r<r'\le6$, $|\langle y_r,y_{r'}\rangle-c_1|\le\tau$ or $|\langle y_r,y_{r'}\rangle-c_2|\le\tau$.
--
--   Then there is a permutation $\sigma$ of $\{0,\dots,6\}$ with
--
--   $$\big|\langle y_i,y_j\rangle-\langle P_{\sigma(i)},P_{\sigma(j)}\rangle\big|\le\tau\qquad\text{for all }i\ne j.$$
--
--   The point is combinatorial: colouring the edges of $K_5$ on the five ring points by "near $c_1$"/"near $c_2$", no triangle can be monochromatic (a Gram-determinant argument), and the only triangle-free 2-colourings of $K_5$ are a pentagon/pentagram pair, which matches the ring of $P$ after relabelling.
--
--   **Formalization Note** All named objects (`pentBipyramid`, `coulombEnergy`, `Base.phi`, `Reg.W`, `Reg.muP`, `Reg.gP`, `Reg.tau`, `Reg.Dpair`, `Reg.Qhess`, `Reg.Pen`, `Glue.TubeRigid`) come from the platform definition `ThomsonN7_core`, taken verbatim from the source; `R3` is `EuclideanSpace ℝ (Fin 3)`.
-- source:
--   H. Tran, Thomson problem N = 7 Lean proof package, https://github.com/huwngtran/thomson-n7-lean @ 25f2fa53119273458cfbb3c4230904bffdd61e53: paper/PAPER.md §7.2 step 3 (rigidity); Lean `ThomsonN7.Glue.tubeRigid_of_le`, https://github.com/huwngtran/thomson-n7-lean/blob/25f2fa53119273458cfbb3c4230904bffdd61e53/formal/lean/ThomsonN7/Solution.lean#L12484

import Definitions.Def_ThomsonN7_core

namespace ThomsonN7

theorem Glue.tubeRigid_of_le {τ : ℝ} (h : τ ≤ 1 / 10) : Glue.TubeRigid τ := by sorry

end ThomsonN7
