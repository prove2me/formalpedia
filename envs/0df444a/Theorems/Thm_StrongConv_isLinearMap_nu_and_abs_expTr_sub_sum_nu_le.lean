-- Prove2me | Theorems.Thm_StrongConv_isLinearMap_nu_and_abs_expTr_sub_sum_nu_le
-- name    : StrongConv.isLinearMap_nu_and_abs_expTr_sub_sum_nu_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:44:41.356966+00:00
-- url     : https://prove2.me/theorems/030b8216-ec84-4170-a5a2-ada8214ab3ad
-- title:
--   Theorem 6.1 — master inequalities
-- statement:
--   Let $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ be self-adjoint of degree at most $q_0$, with $q_0 \ge 1$, and let $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$. Let $\nu_i(h)$ be the $i$-th coefficient of the asymptotic expansion of $\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))]$ in powers of $1/N$ (`nu P i`). Then each $\nu_i$ is linear on real polynomials, and for all $N, m, q \ge 1$ and every real polynomial $h$ of degree at most $q$,
--   $$\Big|\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))] - \sum_{i=0}^{m-1}\frac{\nu_i(h)}{N^i}\Big| \le \frac{(4qq_0(1 + \log d))^{4m}}{N^m}\,\sup_{x\in[-K,K]}|h(x)|.$$
--   The paper asserts the existence of linear functionals $\nu_i$ with this bound. Any such functionals are the coefficients of the expansion, so the statement names them (`nu`), as §§7–9 do.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 20–21, Theorem 6.1 (master inequalities)

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem isLinearMap_nu_and_abs_expTr_sub_sum_nu_le {D d q₀ : ℕ} (P : NCPoly D d)
    (hP : P.IsSelfAdjoint) (hq₀ : P.degree ≤ q₀) (hq₀' : 1 ≤ q₀) :
    (∀ i, IsLinearMap ℝ (nu P i)) ∧
      ∀ N m q : ℕ, 1 ≤ N → 1 ≤ m → 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
        |expTr P N (fun x => h.eval x) - ∑ i ∈ Finset.range m, nu P i h / (N : ℝ) ^ i| ≤
          (4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m *
            cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
  sorry

end StrongConv
