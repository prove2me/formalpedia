-- Prove2me | Theorems.Thm_StrongConv_prob_norm_eval_stableRep_ge_le
-- name    : StrongConv.prob_norm_eval_stableRep_ge_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:58:29.831293+00:00
-- url     : https://prove2.me/theorems/c468442d-ba01-4a11-8a87-66ff101c6ba3
-- title:
--   Theorem 3.14 — strong convergence for stable representations of the symmetric group
-- statement:
--   Fix a stable representation $\pi_N$ of $\mathbf S_N$ (Definition 3.13), defined for $N \ge N_0$ by a character polynomial $\varphi$, with no copy of the trivial representation, and let $\alpha$ be the degree of $D_N = \varphi(N, \dots, N)$ as a polynomial in $N$. There is a constant $C$, depending only on the stable representation, such that for every $d \ge 2$, every self-adjoint $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ of degree at most $q_0$ with $K = \|P\|_{\mathrm M_D(\mathbb C)\otimes C^*(\mathbf F_d)}$, every $0 < \varepsilon < K - \|P(\boldsymbol s, \boldsymbol s^*)\|$ and every $N \ge N_0$:
--   $$\mathbf P\big[\|P(\boldsymbol\Pi^N, \boldsymbol\Pi^{N*})\| \ge \|P(\boldsymbol s, \boldsymbol s^*)\| + \varepsilon\big] \le \frac{CD}N\Big(\frac{Kq_0\log d}{\varepsilon}\Big)^{4(\alpha+1)}\log\Big(\frac{eK}{\varepsilon}\Big),$$
--   where $\boldsymbol\Pi^N = (\pi_N(\sigma_1), \dots, \pi_N(\sigma_d))$ for i.i.d. uniform $\sigma_1, \dots, \sigma_d \in \mathbf S_N$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 14, Theorem 3.14 (stable representations)

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem prob_norm_eval_stableRep_ge_le (π : StableRep) (hπ : π.NoTrivialSummand) :
    ∃ C : ℝ, ∀ D d q₀ : ℕ, 2 ≤ d → ∀ P : NCPoly D d, P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∀ ε : ℝ, 0 < ε → ε < P.fullNorm - ‖P.eval (sLimit d)‖ → ∀ N : ℕ, π.N₀ ≤ N →
      uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ‖P.eval (sLimit d)‖ + ε ≤ ‖P.eval (π.model σ)‖) ≤
        C * D / N * (P.fullNorm * q₀ * Real.log d / ε) ^ (4 * (π.alpha + 1)) *
          Real.log (Real.exp 1 * P.fullNorm / ε) := by
  sorry

end StrongConv
