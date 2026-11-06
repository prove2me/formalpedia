-- Prove2me | Theorems.Thm_StrongConv_prob_norm_eval_sModel_ge_le_without_selfAdjoint
-- name    : StrongConv.prob_norm_eval_sModel_ge_le_without_selfAdjoint
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:49.95458+00:00
-- url     : https://prove2.me/theorems/03584578-7dd4-4dab-808e-2defd21a20bc
-- title:
--   Remark 3.10 — the bound of Theorem 3.9 holds without self-adjointness
-- statement:
--   There is a universal constant $C$ such that for every $d \ge 2$ and every $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree at most $q_0$, self-adjoint or not, with $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$ (the supremum of $\|P(\boldsymbol U, \boldsymbol U^*)\|$ over $d$-tuples of unitary matrices of all dimensions), every $0 < \varepsilon < K - \|P(\boldsymbol s, \boldsymbol s^*)\|$ and every $N$:
--   $$\mathbf P\big[\|P(\boldsymbol S^N, \boldsymbol S^{N*})\| \ge \|P(\boldsymbol s, \boldsymbol s^*)\| + \varepsilon\big] \le C\,\frac DN\Big(\frac{Kq_0\log d}{\varepsilon}\Big)^8\log\Big(\frac{eK}{\varepsilon}\Big).$$
--   Here $\boldsymbol S^N = (S_1^N, \dots, S_d^N)$ are $d$ i.i.d. uniform random $N \times N$ permutation matrices restricted to $\{1_N\}^\perp$, $\boldsymbol s = (\lambda(g_1), \dots, \lambda(g_d))$ are the free generators acting on $l^2(\mathbf F_d)$ by the left-regular representation, and both polynomials act on $D$ copies of the respective space. This is the statement of Theorem 3.9 (`StrongConv.prob_norm_eval_sModel_ge_le`) with the hypothesis that $P$ is self-adjoint removed.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 12, Remark 3.10

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem prob_norm_eval_sModel_ge_le_without_selfAdjoint :
    ∃ C : ℝ, ∀ D d q₀ : ℕ, 2 ≤ d → ∀ P : NCPoly D d, P.degree ≤ q₀ →
      ∀ ε : ℝ, 0 < ε → ε < P.fullNorm - ‖P.eval (sLimit d)‖ → ∀ N : ℕ,
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖P.eval (sLimit d)‖ + ε ≤ ‖P.eval (sModel σ)‖) ≤
        C * (D / N) * (P.fullNorm * q₀ * Real.log d / ε) ^ 8 *
          Real.log (Real.exp 1 * P.fullNorm / ε) := by
  sorry

end StrongConv
