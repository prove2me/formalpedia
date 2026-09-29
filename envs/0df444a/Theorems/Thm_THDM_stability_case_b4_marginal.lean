-- Prove2me | Theorems.Thm_THDM_stability_case_b4_marginal
-- name    : THDM.stability_case_b4_marginal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T00:42:49.514772+00:00
-- url     : https://prove2.me/theorems/3ac45ddc-762c-4711-a9a7-28452854e194
-- title:
--   Section 4, case (b.4): in the marginal case stability holds iff $J_2^2\le C\,J_4$ on $B_3$
-- statement:
--   **Case (b.4) of Section 4 of arXiv:hep-ph/0605184** - the marginal case, and the condition added in version 3 of the paper.
--
--   Suppose that for every $k$ with $|k|\le1$ either $J_4(k)>0$, or $J_4(k)=0$ and $J_2(k)\ge0$, and that $J_4(k)=J_2(k)=0$ occurs for at least one such $k$. Then the potential is bounded from below if and only if there is a constant $C>0$ with
--   $$J_2(k)^2\le C\,J_4(k)\qquad\text{for all }k\in B_3,$$
--   where $B_3=\{k : |k|\le1,\ J_4(k)>0,\ J_2(k)<0\}$. The point is that in the marginal case the sign conditions alone do not decide stability: for fixed $k$ the minimum of $V$ over $K_0\ge0$ is $-J_2(k)^2/(4J_4(k))$, and this family of values is bounded from below exactly under the stated quadratic bound.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 4, p. 7, case (b.4), eqs. (4.9)-(4.10)

import Definitions.Def_THDM_stationary
open scoped BigOperators
open Matrix

namespace THDM

theorem stability_case_b4_marginal
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hm : MarginalCase xi0 xi eta00 eta E) :
    Stable xi0 xi eta00 eta E ↔
      ∃ C : ℝ, 0 < C ∧ ∀ k ∈ B3region xi0 xi eta00 eta E,
        (J2 xi0 xi k) ^ 2 ≤ C * J4 eta00 eta E k := by sorry

end THDM
