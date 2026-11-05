-- Prove2me | Theorems.Thm_StrongConv_not_master_inequalities_printed
-- name    : StrongConv.not_master_inequalities_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T23:13:48.458363+00:00
-- url     : https://prove2.me/theorems/f7bc14ce-577f-4267-92fb-0692350c03d3
-- title:
--   Chen–Garza-Vargas–Tropp–van Handel, Theorem 6.1 for degree 0 is false
-- statement:
--   It is not the case that for every self-adjoint $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree at most $q_0$, for every $q_0 \ge 0$, there are linear functionals $\nu_0, \nu_1, \dots$ on real polynomials such that for all $N, m, q \ge 1$ and every real polynomial $h$ of degree at most $q$,
--   $$\Big|\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))] - \sum_{i=0}^{m-1}\frac{\nu_i(h)}{N^i}\Big| \le \frac{(4qq_0(1 + \log d))^{4m}}{N^m}\,\sup_{x\in[-K,K]}|h(x)|,$$
--   where $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$ (`StrongConv.NCPoly.fullNorm`) and $\mathbf E[\mathrm{tr}_{DN}\,\cdot\,]$ is `StrongConv.expTr`.
--
--   This is Theorem 6.1 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 20), read for every degree: “*Fix a self-adjoint noncommutative polynomial $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree $q_0$ …*”. A constant $P = A \otimes \mathbf 1$ has degree $0$. With $m = 1$ the right-hand side vanishes, so $\nu_0(h)$ would equal $\mathbf E[\mathrm{tr}_{DN}\, h(P)] = (1 - \frac1N)\,\mathrm{tr}_D\, h(A)$ for every $N$ (the normalization of Remark 3.3), which fails for $h = 1$. The mission states the theorem with $q_0 \ge 1$ (`StrongConv.isLinearMap_nu_and_abs_expTr_sub_sum_nu_le`); any $P$ may be treated with $q_0 = 1$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 20, Theorem 6.1 for degree q0 = 0 (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial

namespace StrongConv

theorem not_master_inequalities_printed :
    ¬ ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∃ ν : ℕ → ℝ[X] →ₗ[ℝ] ℝ, ∀ N m q : ℕ, 1 ≤ N → 1 ≤ m → 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
        |expTr P N (fun x => h.eval x) - ∑ i ∈ Finset.range m, ν i h / (N : ℝ) ^ i| ≤
          (4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m *
            cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
  sorry

end StrongConv
