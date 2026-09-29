-- Prove2me | Theorems.Thm_THDM_stability_case_a_and_b2
-- name    : THDM.stability_case_a_and_b2
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:32:24.39692+00:00
-- url     : https://prove2.me/theorems/5d2792e8-577b-4070-949b-2f67e1a00527
-- title:
--   Section 4, cases (a) and (b.2): $J_4<0$ somewhere gives instability, $J_4>0$ everywhere gives stability
-- statement:
--   **Cases (a) and (b.2) of Section 4 of arXiv:hep-ph/0605184.** With $V(K_0,k)=K_0J_2(k)+K_0^2J_4(k)$ on the domain $K_0\ge0$, $|k|\le1$:
--
--   (a) if $J_4(k)<0$ for some $k$ with $|k|\le1$, the potential is unstable, i.e. not bounded from below;
--
--   (b.2) if $J_4(k)>0$ for all $k$ with $|k|\le1$ - stability in the strong sense (4.4) - the potential is bounded from below. The paper's argument is the completion of the square (4.5), which also gives $V\to\infty$ along every path with $K_0\to\infty$ (4.6).
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 4, pp. 6-7, cases (a) and (b.2), eqs. (4.4)-(4.6)

import Definitions.Def_THDM_stationary
open scoped BigOperators
open Matrix

namespace THDM

theorem stability_case_a_and_b2
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) :
    ((∃ k ∈ ballK, J4 eta00 eta E k < 0) → ¬ Stable xi0 xi eta00 eta E) ∧
    (StrongStable eta00 eta E → Stable xi0 xi eta00 eta E) := by sorry

end THDM
