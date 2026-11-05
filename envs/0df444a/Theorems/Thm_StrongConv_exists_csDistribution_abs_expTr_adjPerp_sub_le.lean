-- Prove2me | Theorems.Thm_StrongConv_exists_csDistribution_abs_expTr_adjPerp_sub_le
-- name    : StrongConv.exists_csDistribution_abs_expTr_adjPerp_sub_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:48:45.802835+00:00
-- url     : https://prove2.me/theorems/32eccad6-14c3-4a39-8ad2-7ec725aa1877
-- title:
--   Lemma 8.1 — second-order expansion of the spectral statistics of a random regular graph
-- statement:
--   There is a universal constant $C$ such that for every $d$ there is a compactly supported distribution $\nu_1$ (Definition 4.6) with
--   $$\Big|\mathbf E[\mathrm{tr}_N\, h(A^N)] - \tau(h(A_{\rm F})) - \frac1N\nu_1(h)\Big| \le C\,\frac{(1 + \log d)^8}{N^2}\,\beta_*\,\|f^{(9)}\|_{L^\beta[0,2\pi]}$$
--   for all $N \ge 1$, $\beta > 1$ and $h \in C^\infty(\mathbb R)$, where $f(\theta) = h(2d\cos\theta)$, $1/\beta_* = 1 - 1/\beta$, $A^N$ is the random $2d$-regular adjacency matrix restricted to $\{1_N\}^\perp$, $A_{\rm F}$ is the adjacency operator of the $2d$-regular tree on $l^2(\mathbf F_d)$, and $\tau(h(A_{\rm F}))$ is taken as a real number (its real part).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 23, Lemma 8.1

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem exists_csDistribution_abs_expTr_adjPerp_sub_le :
    ∃ C : ℝ, ∀ d : ℕ, ∃ ν₁ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution ν₁ ∧
      ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
        |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (fnCalc (h : ℝ → ℝ) (adjPerp σ))) -
            (tau (fnCalc (h : ℝ → ℝ) (adjFree d))).re - ν₁ h / N| ≤
          C * (1 + Real.log d) ^ 8 / (N : ℝ) ^ 2 * conjExp β *
            lpNormCircle β (iteratedDeriv 9 (fun θ => (h : ℝ → ℝ) (2 * d * Real.cos θ))) := by
  sorry

end StrongConv
