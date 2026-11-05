-- Prove2me | Theorems.Thm_StrongConv_not_quantitative_weak_convergence_printed
-- name    : StrongConv.not_quantitative_weak_convergence_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T23:13:51.218+00:00
-- url     : https://prove2.me/theorems/1cc29e3a-898f-47f3-83ef-cb0891203efa
-- title:
--   Chen–Garza-Vargas–Tropp–van Handel, Corollary 7.2 as printed is false
-- statement:
--   There is no constant $C$ such that for every self-adjoint $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree at most $q_0$, with $q_0 \ge 1$, and all $N \ge 1$, $\beta > 1$ and $h \in C^\infty(\mathbb R)$,
--   $$\big|\mathbf E[\mathrm{tr}_{DN}\, h(P(\boldsymbol S^N, \boldsymbol S^{N*}))] - (\mathrm{tr}_D \otimes \tau)(h(P(\boldsymbol s, \boldsymbol s^*)))\big| \le C\,\frac{(q_0(1+\log d))^4}{N}\,\beta_*\,\|f^{(5)}\|_{L^\beta[0,2\pi]},$$
--   where $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$, $f(\theta) = h(K\cos\theta)$ and $1/\beta_* = 1 - 1/\beta$.
--
--   This is Corollary 7.2 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 23), with $\lesssim$ read as a universal constant. For $h = 1$ the right-hand side is $0$, because $f$ is constant, while the left-hand side is $\frac1N$: $\mathbf E[\mathrm{tr}_{DN}\,\mathbf 1] = 1 - \frac1N$ under the normalization of Remark 3.3, and $(\mathrm{tr}_D \otimes \tau)(\mathbf 1) = 1$. The mission adds $\frac1N\sup_{[-K,K]}|h|$ to the right-hand side (`StrongConv.norm_expTr_sub_trTau_le`), the constant term of the Chebyshev expansion of $h$ that the proof of Theorem 7.1 treats as cancelling.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 23, Corollary 7.2 as printed (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial

namespace StrongConv

theorem not_quantitative_weak_convergence_printed :
    ¬ ∃ C : ℝ, ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint → P.degree ≤ q₀ → 1 ≤ q₀ →
      ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
        ‖(expTr P N (h : ℝ → ℝ) : ℂ) - trTau (fnCalc (h : ℝ → ℝ) (P.eval (sLimit d)))‖ ≤
          C * (q₀ * (1 + Real.log d)) ^ 4 / N * conjExp β *
            lpNormCircle β (iteratedDeriv 5 (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) := by
  sorry

end StrongConv
