-- Prove2me | Theorems.Thm_StrongConv_exists_csDistribution_abs_expTr_sub_le
-- name    : StrongConv.exists_csDistribution_abs_expTr_sub_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:46:39.830076+00:00
-- url     : https://prove2.me/theorems/93cdd62a-5d35-4b00-90b8-808eeebdfd97
-- title:
--   Theorem 7.1 — smooth master inequalities
-- statement:
--   There is a universal constant $C$ with the following property. Let $P$ be self-adjoint of degree at most $q_0$, and let $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$. Then there are compactly supported distributions $\nu_0, \nu_1, \dots$ (Definition 4.6), each agreeing on real polynomials with the expansion coefficient `nu P i` of Theorem 6.1, such that for all $N \ge 1$, $m \ge 2$, $\beta > 1$ and $h \in C^\infty(\mathbb R)$,
--   $$\Big|\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))] - \sum_{i=0}^{m-1}\frac{\nu_i(h)}{N^i}\Big| \le C\,\frac{(4q_0(1+\log d))^{4m}}{N^m}\,\beta_*\,\|f^{(4m+1)}\|_{L^\beta[0,2\pi]},$$
--   where $f(\theta) = h(K\cos\theta)$ and $1/\beta_* = 1 - 1/\beta$. The paper's $\lesssim$ is read as a universal constant.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 22, Theorem 7.1 (smooth master inequalities)

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem exists_csDistribution_abs_expTr_sub_le :
    ∃ C : ℝ, ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∃ ν : ℕ → smoothFun →ₗ[ℝ] ℝ,
        (∀ i, IsCSDistribution (ν i) ∧ ∀ h : ℝ[X], ν i (polyFun h) = nu P i h) ∧
        ∀ N m : ℕ, 1 ≤ N → 2 ≤ m → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
          |expTr P N (h : ℝ → ℝ) - ∑ i ∈ Finset.range m, ν i h / (N : ℝ) ^ i| ≤
            C * (4 * q₀ * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * conjExp β *
              lpNormCircle β (iteratedDeriv (4 * m + 1) (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) := by
  sorry

end StrongConv
