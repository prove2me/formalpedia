-- Prove2me | Theorems.Thm_StrongConv_not_abs_nu_le_printed
-- name    : StrongConv.not_abs_nu_le_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T23:13:52.686409+00:00
-- url     : https://prove2.me/theorems/589dddcb-87c6-435a-bce7-8fe178706d4f
-- title:
--   Chen–Garza-Vargas–Tropp–van Handel, Corollary 6.2 for degree 0 is false
-- statement:
--   It is not the case that for every self-adjoint $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree at most $q_0$, for every $q_0 \ge 0$, every $m \ge 0$, $q \ge 1$ and every real polynomial $h$ of degree at most $q$,
--   $$|\nu_m(h)| \le (4qq_0(1 + \log d))^{4m}\,\sup_{x\in[-K,K]}|h(x)|,$$
--   where $\nu_m(h)$ is the $m$-th coefficient of the expansion of $\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))]$ in powers of $1/N$ (`StrongConv.nu`) and $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$.
--
--   This is Corollary 6.2 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 21), “*In the setting of Theorem 6.1*”, read for every degree. A constant $P = A \otimes \mathbf 1$ has degree $0$ and $\mathbf E[\mathrm{tr}_{DN}\, h(P)] = (1 - \frac1N)\,\mathrm{tr}_D\, h(A)$ (the normalization of Remark 3.3), so $\nu_1(h) = -\mathrm{tr}_D\, h(A)$, which the bound with $q_0 = 0$ and $m = 1$ would force to vanish. The mission states the corollary with $q_0 \ge 1$ (`StrongConv.abs_nu_le`).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 21, Corollary 6.2 for degree q0 = 0 (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial

namespace StrongConv

theorem not_abs_nu_le_printed :
    ¬ ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∀ (m q : ℕ), 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
        |nu P m h| ≤ (4 * q * q₀ * (1 + Real.log d)) ^ (4 * m) *
          cNorm 0 (fun x => h.eval x) (-P.fullNorm) P.fullNorm := by
  sorry

end StrongConv
