-- Prove2me | Theorems.Thm_ReviewProvision_lemma_2
-- name    : ReviewProvision.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:09.678586+00:00
-- url     : https://prove2.me/theorems/5d062e6f-9140-4a34-9501-7f20c2ffd1b5
-- title:
--   Lemma 2, p.17 — profit increases in the variance
-- statement:
--   The function $\Pi_2$ is strictly increasing on $[0,\infty)$. Consequently, fix feasible sales $\vec k$ and two policies $\psi,\psi'$ with $\mathrm{Var}[v_{\psi n}]\le\mathrm{Var}[v_{\psi'n}]$ in every cluster. Then
--
--   $$
--   \Pi_\psi(\vec k)\le\Pi_{\psi'}(\vec k),
--   $$
--
--   with strict inequality if the variances differ in some cluster.
--
--   At given sales, what a policy is worth to the firm is therefore measured by the variance of the customer evaluation that it induces.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - generalization: symmetric first-period price k and a single σ_ψ(k) → any feasible ~k, compared cluster by cluster; reason: the symmetric case has all clusters' variances equal; the proof of Proposition 4 needs the cluster-wise form on Lemma 11
--   - reading: 'increases' → strictly increasing, and strict profit comparison when a variance is strictly larger; reason: the stronger reading; the derivative is positive by Lemma 8
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), Lemma 2, p.17

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Lemma 2**, SSRN 3403322 (manuscript of 2021-05-24), p.17 (PDF 17): the firm's profit increases
in the a priori standard deviation. `Π_2` is strictly increasing on `[0, ∞)`. Hence, at fixed sales, a
policy with larger variances in every cluster earns at least as much, and strictly more if one
variance is strictly larger.

**Formalization Note.** The page is for symmetric sales; the cluster-wise form is what the proof of
Proposition 3 needs. -/
theorem lemma_2 (p : Params) {N : ℕ} :
    StrictMonoOn Pi2 (Set.Ici 0) ∧
    ∀ (ψ ψ' : Policy) (k : Fin N → ℝ), Feasible k →
      (∀ n, Var[posteriorMean p k ψ n; prior p N] ≤ Var[posteriorMean p k ψ' n; prior p N]) →
      profit p ψ k ≤ profit p ψ' k ∧
      ((∃ n, Var[posteriorMean p k ψ n; prior p N] < Var[posteriorMean p k ψ' n; prior p N]) →
        profit p ψ k < profit p ψ' k) := by sorry

end ReviewProvision
