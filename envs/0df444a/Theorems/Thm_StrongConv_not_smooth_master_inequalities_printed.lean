-- Prove2me | Theorems.Thm_StrongConv_not_smooth_master_inequalities_printed
-- name    : StrongConv.not_smooth_master_inequalities_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T23:13:52.480602+00:00
-- url     : https://prove2.me/theorems/57a94cac-d566-423b-97e7-dc26a3f093de
-- title:
--   Chen–Garza-Vargas–Tropp–van Handel, Theorem 7.1 at m = 1 is false
-- statement:
--   There is no constant $C$ such that for every self-adjoint $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree at most $q_0$ there are compactly supported distributions $\nu_0, \nu_1, \dots$ (`StrongConv.IsCSDistribution`) with
--   $$\Big|\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))] - \sum_{i=0}^{m-1}\frac{\nu_i(h)}{N^i}\Big| \le C\,\frac{(4q_0(1+\log d))^{4m}}{N^m}\,\beta_*\,\|f^{(4m+1)}\|_{L^\beta[0,2\pi]}$$
--   for all $N, m \ge 1$, $\beta > 1$ and $h \in C^\infty(\mathbb R)$, where $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$, $f(\theta) = h(K\cos\theta)$ and $1/\beta_* = 1 - 1/\beta$.
--
--   This is Theorem 7.1 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 22), over its printed range “*for all $N, m \in \mathbb N$, $\beta > 1$, $h \in C^\infty(\mathbb R)$*”, with $\lesssim$ read as a universal constant. At $m = 1$ and $h = 1$ the right-hand side is $0$, because $f$ is constant, so $\nu_0(1)$ would equal $\mathbf E[\mathrm{tr}_{DN}\,\mathbf 1] = 1 - \frac1N$ (the normalization of Remark 3.3) for every $N$. The proof on p. 23 takes $\nu_i(h) = 0$ for $i \ge 1$ when $h$ is constant; in fact $\nu_1(1) = -1$. The mission states the theorem for $m \ge 2$ (`StrongConv.exists_csDistribution_abs_expTr_sub_le`), which covers every application in the paper, and the case $m = 1$ with the missing term as Corollary 7.2 (`StrongConv.norm_expTr_sub_trTau_le`).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 22, Theorem 7.1 at m = 1 (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial

namespace StrongConv

theorem not_smooth_master_inequalities_printed :
    ¬ ∃ C : ℝ, ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∃ ν : ℕ → smoothFun →ₗ[ℝ] ℝ, (∀ i, IsCSDistribution (ν i)) ∧
        ∀ N m : ℕ, 1 ≤ N → 1 ≤ m → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
          |expTr P N (h : ℝ → ℝ) - ∑ i ∈ Finset.range m, ν i h / (N : ℝ) ^ i| ≤
            C * (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * conjExp β *
              lpNormCircle β (iteratedDeriv (4 * m + 1)
                (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) := by
  sorry

end StrongConv
