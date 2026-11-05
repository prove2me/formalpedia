-- Prove2me | Theorems.Thm_StrongConv_tendsto_prob_norm_eval_stableRep_ge_sub
-- name    : StrongConv.tendsto_prob_norm_eval_stableRep_ge_sub
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:58:54.496189+00:00
-- url     : https://prove2.me/theorems/e5cb2670-c473-4330-afa1-839e288ae8f6
-- title:
--   Theorem A.1 — the strong convergence lower bound, ‖P(Πᴺ, Πᴺ*)‖ ≥ ‖P(s, s*)‖ − o(1)
-- statement:
--   Fix a stable representation $\pi_N$ of $\mathbf S_N$ (Definition 3.13) on nonzero spaces ($D_N \ge 1$ for $N \ge N_0$) with no copy of the trivial representation, and any $P \in \mathrm M_D(\mathbb C) \otimes \mathbb C\langle \boldsymbol s, \boldsymbol s^*\rangle$ (not necessarily self-adjoint). For every $\delta > 0$,
--   $$\mathbf P\big[\|P(\boldsymbol\Pi^N, \boldsymbol\Pi^{N*})\| \ge \|P(\boldsymbol s, \boldsymbol s^*)\| - \delta\big] \to 1 \quad (N \to \infty),$$
--   where $\boldsymbol\Pi^N = (\pi_N(\sigma_1), \dots, \pi_N(\sigma_d))$ for i.i.d. uniform $\sigma_1, \dots, \sigma_d \in \mathbf S_N$.
--
--   The hypothesis $D_N \ge 1$ excludes the zero representation ($\varphi = 0$, $D_N = 0$), which satisfies Definition 3.13 vacuously. For it, $\|P(\boldsymbol\Pi^N, \boldsymbol\Pi^{N*})\| = 0$, and the conclusion fails whenever $P(\boldsymbol s, \boldsymbol s^*) \ne 0$ ([`StrongConv.not_tendsto_prob_norm_eval_stableRep_ge_sub_printed`](https://prove2.me/theorems/5871a3dd-c182-450e-932b-baa87426d501)).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 33, Theorem A.1 (lower bound)

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology

namespace StrongConv

theorem tendsto_prob_norm_eval_stableRep_ge_sub (π : StableRep) (hπ : π.NoTrivialSummand)
    (hdim : ∀ N, π.N₀ ≤ N → 0 < π.dim N) {D d : ℕ} (P : NCPoly D d) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      ‖P.eval (sLimit d)‖ - δ ≤ ‖P.eval (π.model σ)‖)) atTop (𝓝 1) := by
  sorry

end StrongConv
