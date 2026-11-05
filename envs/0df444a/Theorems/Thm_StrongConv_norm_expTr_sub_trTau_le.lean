-- Prove2me | Theorems.Thm_StrongConv_norm_expTr_sub_trTau_le
-- name    : StrongConv.norm_expTr_sub_trTau_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:47:51.202199+00:00
-- url     : https://prove2.me/theorems/eab595ae-4056-4b4c-86fc-4e09163a2d54
-- title:
--   Corollary 7.2 — quantitative weak convergence
-- statement:
--   There is a universal constant $C$ with the following property. Let $P$ be self-adjoint of degree at most $q_0$, and let $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$. Then for all $N \ge 1$, $\beta > 1$ and $h \in C^\infty(\mathbb R)$,
--   $$\big|\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))] - (\mathrm{tr}_D \otimes \tau)(h(P(\boldsymbol s, \boldsymbol s^*)))\big| \le C\,\frac{(q_0(1+\log d))^4}{N}\,\beta_*\,\|f^{(5)}\|_{L^\beta[0,2\pi]} + \frac1N\sup_{x\in[-K,K]}|h(x)|,$$
--   with $f(\theta) = h(K\cos\theta)$ and $1/\beta_* = 1 - 1/\beta$. The difference is taken in $\mathbb C$, so the statement also bounds the imaginary part of $(\mathrm{tr}_D \otimes \tau)(h(P(\boldsymbol s, \boldsymbol s^*)))$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 23, Corollary 7.2 (quantitative weak convergence)

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem norm_expTr_sub_trTau_le :
    ∃ C : ℝ, ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
        ‖(expTr P N (h : ℝ → ℝ) : ℂ) - trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d)))‖ ≤
          C * (q₀ * (1 + Real.log d)) ^ 4 / N * conjExp β *
            lpNormCircle β (iteratedDeriv 5 (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) +
          cNorm 0 (h : ℝ → ℝ) (-P.fullNorm) P.fullNorm / N := by
  sorry

end StrongConv
