-- Prove2me | Theorems.Thm_ReviewProvision_proposition_4
-- name    : ReviewProvision.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:57:52.801999+00:00
-- url     : https://prove2.me/theorems/c86985d7-05d0-4ac4-82b0-62a36bbf7bfa
-- title:
--   Proposition 4, p.24, with §5.2, p.25 — JP attains the FP optimum and strictly beats AP and GP
-- statement:
--   Let $N\ge2$ and let the parameters be arbitrary. Then:
--
--   1. $\Pi_J(\vec k)\le\Pi_F(\vec k)$ for all feasible sales $\vec k$;
--   2. there is $k_0>0$ such that $\vec k^s=(k_0,\dots,k_0)$ is optimal for FP, and every optimum of FP equals $\vec k^s$;
--   3. $\vec k^s$ is optimal for JP, and
--
--   $$
--   \Pi_J(\vec k^s)=\Pi_F(\vec k^s),
--   $$
--
--   that is, $\Pi^*_J=\Pi^*_F$, with $\Pi^*_J$ achieved at the optimal symmetric sales;
--   4. AP has an optimum $\vec k_A$, and $\Pi_A(\vec k_A)<\Pi_J(\vec k^s)$;
--   5. GP has an optimum $\vec k_G$, and $\Pi_G(\vec k_G)<\Pi_J(\vec k^s)$.
--
--   A firm that shows each customer only the own-cluster review and the global average earns the full-information optimum, and strictly more than with either signal alone.
--
--   **Formalization Note** The profit is built from conditional expectations of the Gaussian model, not from the closed-form variances, so the Bayesian update is part of the statement.
--
--   Differences from the source:
--   - reading: the feasible sales are not stated → k_n ≥ 0 for all n, with no upper bound; reason: the proofs use k_N ≥ 0 and evaluate at k_N = 0 (pp.37, 44); (27) has no multiplier, and an upper bound k_n ≤ 1 is not intended since the optimum can exceed 1
--   - reading: 'more profitable than both AP and GP' (§5.2) → strict inequality; reason: the stronger reading; the printed proof gives ≥, and strictness follows from uniqueness of the FP optimum, Lemma 11 and Lemma 2
--   - generalization: Assumption 1 restricts AP and GP (p.16) → no Assumption 1; reason: under Assumption 1 the optimum over all ~k is the paper's Π*_ψ by Proposition 1, so the statement specializes to the source
--   - reading: optimal profit Π*_ψ → the value at a maximizer, with existence of the optima in the conclusion; reason: no supremum over ~k is taken; Π_ψ is continuous on k ≥ 0 and tends to −∞
--   - encoding: prices p_{n1}, prior mean q_p, ratings r_n, clusters {1, …, N} → sales k_n, q_p = 1, the statistic y_n = w_n(q + t_n) + √w_n ε_n, Fin N; reason: as in (6) and §3.1; y_n = w_n r_n when w_n > 0 and is 0 when no ratings exist
--   - generalization: Π*_J = Π*_F, achieved under the optimal symmetric first-period pricing strategy → also: the FP optimum is unique and equals (k₀, …, k₀) with k₀ > 0 (Proposition 3, p.23, and p.45); reason: the extra clause names the point at which Π*_J = Π*_F; dropping it gives the printed statement
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), Proposition 4, p.24; §5.2, p.25

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Proposition 4 with the dominance of §5.2**, SSRN 3403322 (manuscript of 2021-05-24), p.24 and p.25
(PDF 24–25): for arbitrary first-period sales the firm's profit under JP is no higher than under FP;
the optimal profits under the two policies are equal, `Π*_J = Π*_F`, and `Π*_J` is achieved at the
optimal symmetric first-period sales; and JP is more profitable than both AP and GP.

For `N ≥ 2`: (1) `Π_J(~k) ≤ Π_F(~k)` for every feasible `~k`; (2) there is `k₀ > 0` such that
`~k^s = (k₀, …, k₀)` is optimal for FP, and every optimum of FP equals `~k^s`; (3) `~k^s` is optimal for
JP, with `Π_J(~k^s) = Π_F(~k^s)`; (4), (5) AP and GP each have an optimum, with profit strictly below
`Π_J(~k^s)`.

**Formalization Note.** `profit` is built from conditional expectations of the Gaussian model, not
from the closed-form variances. Sales `k_n ≥ 0` have no upper bound. "More profitable" is strict.
Optima are maximizers, so `Π*_ψ` exists by assertion. Assumption 1 is not assumed. -/
theorem proposition_4 (p : Params) {N : ℕ} (hN : 2 ≤ N) :
    (∀ k : Fin N → ℝ, Feasible k → profit p .JP k ≤ profit p .FP k) ∧
    ∃ k₀ : ℝ, 0 < k₀ ∧
      IsOptimal p .FP (fun _ : Fin N => k₀) ∧
      (∀ k : Fin N → ℝ, IsOptimal p .FP k → k = fun _ => k₀) ∧
      IsOptimal p .JP (fun _ : Fin N => k₀) ∧
      profit p .JP (fun _ : Fin N => k₀) = profit p .FP (fun _ : Fin N => k₀) ∧
      (∃ kA : Fin N → ℝ, IsOptimal p .AP kA ∧
        profit p .AP kA < profit p .JP (fun _ : Fin N => k₀)) ∧
      (∃ kG : Fin N → ℝ, IsOptimal p .GP kG ∧
        profit p .GP kG < profit p .JP (fun _ : Fin N => k₀)) := by sorry

end ReviewProvision
