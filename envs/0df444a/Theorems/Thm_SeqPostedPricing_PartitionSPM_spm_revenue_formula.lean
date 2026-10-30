-- Prove2me | Theorems.Thm_SeqPostedPricing_PartitionSPM_spm_revenue_formula
-- name    : SeqPostedPricing.PartitionSPM.spm_revenue_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:05.591341+00:00
-- url     : https://prove2.me/theorems/c8d6b618-fe05-422a-b027-5e9b58fadc0c
-- title:
--   Revenue formula $R^\sigma_p = \sum_i c_i q_i p_i$ for an SPM
-- statement:
--   Let the values be independent with laws $\mu_i$ and consider a sequential posted-price mechanism with prices $p$, order $\sigma$ and an arbitrary feasibility constraint. Let $c_t$ be the probability that the agent $\sigma(t)$ of step $t$ is offered service. Then the expected revenue is
--
--   $$
--   R^\sigma_p = \sum_{t} c_t \, \Pr\big[v_{\sigma(t)} \ge p_{\sigma(t)}\big] \, p_{\sigma(t)} .
--   $$
--
--   When $F_i$ has no atom at $p_i$ the middle factor is $q_i = 1 - F_i(p_i)$, which is the paper's formula $R^\sigma_p = \sum_i c_i q_i p_i$. It reduces revenue comparisons of SPMs to comparisons of the offer probabilities.
--
--   **Formalization Note** The mechanism may also be restricted to a set of active agents (inactive agents are never offered); with every agent active it is the paper's SPM.
--
--   Differences from the source:
--   - generalization: q_i = 1 − F_i(p_i) (distributions with densities) → Pr[v_i ≥ p_i] for arbitrary probability measures; reason: the two agree when there is no atom at p_i, in particular for the distributions with densities of §2.1
--   - generalization: the SPM offers every agent → an SPM restricted to a set of active agents; reason: taking every agent active gives the paper's SPM
--   - encoding: a rational agent accepts iff the price is no more than its value → acceptance is p_i ≤ v_i; reason: the paper's rule (§1); with a density Pr[v_i ≥ p_i] = 1 − F_i(p_i) = q_i
--   - encoding: agents 1, …, n and an ordering σ → `Fin n` and σ : Fin n ≃ Fin n mapping the step to the agent offered at it; reason: Lean indexing convention; the same instances
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, unnumbered, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_spmOffered
import Definitions.Def_SeqPostedPricing_PartitionSPM_spmRevenue

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory

/-- **Revenue formula for an SPM** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, unnumbered, p. 4 = PDF p. 6): "Let ci denote the
probability taken over values of agents σ(1), · · · , σ(i − 1) that the mechanism offers to serve
agent i, and let qi = 1 − Fi(pi). Then the expected revenue of the sequential mechanism, R^σ_p, is
given by Σ_i ci qi pi."

For independent values `v_i ∼ μ_i`, any feasibility constraint, prices, set of active agents and
order, the expected revenue of the SPM is `Σ_t c_t · Pr[v_{σ t} ≥ p_{σ t}] · p_{σ t}`, where `c_t` is
the probability that the agent of step `t` is offered service.

**Formalization Note** The paper's `q_i = 1 − F_i(p_i) = Pr[v_i > p_i]`; with acceptance `p_i ≤ v_i`
the exact factor is `Pr[v_i ≥ p_i]`, which equals `1 − F_i(p_i)` whenever `μ_i` has no atom at
`p_i` (in particular for the distributions with densities of §2.1). The formula is stated for
arbitrary probability measures. Steps are 0-based. -/
theorem spm_revenue_formula {n : ℕ} (Feas : Finset (Fin n) → Prop)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n) :
    spmRevenue Feas μ p active σ =
      ∑ t : Fin n, (Measure.pi μ {v | spmOffered Feas p active σ v t}).toReal
        * (μ (σ t) (Set.Ici (p (σ t)))).toReal * p (σ t) := by sorry

end SeqPostedPricing.PartitionSPM
