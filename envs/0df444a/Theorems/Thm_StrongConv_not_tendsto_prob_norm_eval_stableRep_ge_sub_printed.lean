-- Prove2me | Theorems.Thm_StrongConv_not_tendsto_prob_norm_eval_stableRep_ge_sub_printed
-- name    : StrongConv.not_tendsto_prob_norm_eval_stableRep_ge_sub_printed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T23:13:50.909531+00:00
-- url     : https://prove2.me/theorems/5871a3dd-c182-450e-932b-baa87426d501
-- title:
--   Chen–Garza-Vargas–Tropp–van Handel, Theorem A.1 fails for the zero representation
-- statement:
--   It is not the case that for every stable representation $\pi_N$ of $\mathbf S_N$ (Definition 3.13, `StrongConv.StableRep`) with no copy of the trivial representation, every $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ and every $\delta > 0$,
--   $$\mathbf P\big[\|P(\boldsymbol\Pi^N, \boldsymbol\Pi^{N*})\| \ge \|P(\boldsymbol s, \boldsymbol s^*)\| - \delta\big] \to 1 \quad (N \to \infty),$$
--   where $\boldsymbol\Pi^N = (\pi_N(\sigma_1), \dots, \pi_N(\sigma_d))$ for i.i.d. uniform $\sigma_1, \dots, \sigma_d \in \mathbf S_N$.
--
--   This is Theorem A.1 of C.-F. Chen, J. Garza-Vargas, J. A. Tropp and R. van Handel, *A new approach to strong convergence*, Ann. of Math. (2) 203 (2026) 555–602 (arXiv v3, p. 33), for “*any stable representation as in section 3.4.2*”. The zero representation ($\varphi = 0$, $D_N = 0$) satisfies Definition 3.13 vacuously and has no trivial summand. For it $\|P(\boldsymbol\Pi^N, \boldsymbol\Pi^{N*})\| = 0$, so the conclusion fails whenever $\|P(\boldsymbol s, \boldsymbol s^*)\| > \delta$. The mission states the theorem for representations on nonzero spaces, $D_N \ge 1$ (`StrongConv.tendsto_prob_norm_eval_stableRep_ge_sub`).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 33, Theorem A.1 for every stable representation, the zero representation included (printed-fails lemma, not in the paper)

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology Polynomial

namespace StrongConv

theorem not_tendsto_prob_norm_eval_stableRep_ge_sub_printed :
    ¬ ∀ (π : StableRep), π.NoTrivialSummand → ∀ {D d : ℕ} (P : NCPoly D d) (δ : ℝ), 0 < δ →
      Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ‖P.eval (sLimit d)‖ - δ ≤ ‖P.eval (π.model σ)‖)) atTop (𝓝 1) := by
  sorry

end StrongConv
