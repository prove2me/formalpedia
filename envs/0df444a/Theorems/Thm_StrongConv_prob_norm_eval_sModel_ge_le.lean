-- Prove2me | Theorems.Thm_StrongConv_prob_norm_eval_sModel_ge_le
-- name    : StrongConv.prob_norm_eval_sModel_ge_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:59:22.86281+00:00
-- url     : https://prove2.me/theorems/cbc45abf-5c6f-4b43-a6f7-f453bfb66fbc
-- title:
--   Theorem 3.9 — strong convergence of random permutation matrices, with a rate
-- statement:
--   There is a universal constant $C$ such that for every $d \ge 2$ and every self-adjoint $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree at most $q_0$, with $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$ (the supremum of $\|P(\boldsymbol U, \boldsymbol U^*)\|$ over $d$-tuples of unitary matrices of all dimensions), every $0 < \varepsilon < K - \|P(\boldsymbol s, \boldsymbol s^*)\|$ and every $N$:
--   $$\mathbf P\big[\|P(\boldsymbol S^N, \boldsymbol S^{N*})\| \ge \|P(\boldsymbol s, \boldsymbol s^*)\| + \varepsilon\big] \le C\,\frac DN\Big(\frac{Kq_0\log d}{\varepsilon}\Big)^8\log\Big(\frac{eK}{\varepsilon}\Big).$$
--   Here $\boldsymbol S^N = (S_1^N, \dots, S_d^N)$ are $d$ i.i.d. uniform random $N \times N$ permutation matrices restricted to $\{1_N\}^\perp$, $\boldsymbol s = (\lambda(g_1), \dots, \lambda(g_d))$ are the free generators acting on $l^2(\mathbf F_d)$ by the left-regular representation, and both polynomials act on $D$ copies of the respective space. The paper's $\lesssim$ is read as a universal constant, and $\varepsilon > 0$ is read in.
--
--   Chen–Garza-Vargas–Tropp–van Handel, p. 12: “**Theorem 3.9.** *Let $d \ge 2$, and let $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ be any self-adjoint noncommutative polynomial of degree $q_0$. Then we have* $$\mathbf P\big[\|P(\boldsymbol S^N, \boldsymbol S^{N*})\| \ge \|P(\boldsymbol s, \boldsymbol s^*)\| + \varepsilon\big] \lesssim \frac DN\Big(\frac{Kq_0\log d}{\varepsilon}\Big)^8\log\Big(\frac{eK}{\varepsilon}\Big)$$ *for all $\varepsilon < K - \|P(\boldsymbol s, \boldsymbol s^*)\|$, where $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$.*”
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 12, Theorem 3.9 (strong convergence of random permutation matrices)

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem prob_norm_eval_sModel_ge_le :
    ∃ C : ℝ, ∀ D d q₀ : ℕ, 2 ≤ d → ∀ P : NCPoly D d, P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∀ ε : ℝ, 0 < ε → ε < P.fullNorm - ‖P.eval (sLimit d)‖ → ∀ N : ℕ,
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖P.eval (sLimit d)‖ + ε ≤ ‖P.eval (sModel σ)‖) ≤
        C * (D / N) * (P.fullNorm * q₀ * Real.log d / ε) ^ 8 *
          Real.log (Real.exp 1 * P.fullNorm / ε) := by
  sorry

end StrongConv
