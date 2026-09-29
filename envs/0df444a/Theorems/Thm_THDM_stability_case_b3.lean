-- Prove2me | Theorems.Thm_THDM_stability_case_b3
-- name    : THDM.stability_case_b3
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:35:05.235341+00:00
-- url     : https://prove2.me/theorems/5a750378-64e1-49e4-bd40-d20a885526f3
-- title:
--   Section 4, case (b.3): stability in the weak sense implies boundedness from below
-- statement:
--   **Case (b.3) of Section 4 of arXiv:hep-ph/0605184.** Suppose that for every $k$ with $|k|\le1$ either $J_4(k)>0$, or $J_4(k)=0$ and $J_2(k)>0$ - this is stability in the weak sense (4.7). Then the potential $V(K_0,k)=K_0J_2(k)+K_0^2J_4(k)$ is bounded from below on $K_0\ge0$, $|k|\le1$. The paper proves it by splitting the ball into the compact regions $B_0,B_1,B_2$ of (4.8) and bounding $V$ separately on each.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 4, pp. 6-7, case (b.3), eqs. (4.7)-(4.8)

import Definitions.Def_THDM_stationary
open scoped BigOperators
open Matrix

namespace THDM

theorem stability_case_b3
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) :
    WeakStable xi0 xi eta00 eta E → Stable xi0 xi eta00 eta E := by sorry

end THDM
