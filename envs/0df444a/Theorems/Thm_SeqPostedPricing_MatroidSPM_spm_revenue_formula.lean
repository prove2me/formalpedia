-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_spm_revenue_formula
-- name    : SeqPostedPricing.MatroidSPM.spm_revenue_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:43:10.605583+00:00
-- url     : https://prove2.me/theorems/07714365-145e-497a-9056-0d24466b441f
-- title:
--   §2.2: $\mathcal R^\sigma_{\mathbf p}=\sum_i c_iq_ip_i$
-- statement:
--   Let the values be independent, $v_i\sim\mu_i$ (any probability distributions), and consider the SPM with feasibility constraint $\mathcal J$, prices $\mathbf p$, set of agents it makes offers to, and order $\sigma$. Let $c_t$ be the probability that the agent $\sigma(t)$ of step $t$ is offered service, and $q_{\sigma(t)}=\Pr[v_{\sigma(t)}\ge p_{\sigma(t)}]$ its acceptance probability. Then
--
--   $$
--   \mathcal R^\sigma_{\mathbf p}=\sum_{t} c_t\,q_{\sigma(t)}\,p_{\sigma(t)} .
--   $$
--
--   The formula separates the probability of reaching an agent with a feasible offer from the agent's own acceptance decision, which is independent of it.
--
--   Differences from the source:
--   - generalization: q_i = 1 − F_i(p_i), distributions with densities → q = Pr[v ≥ p] = μ([p, ∞)) for arbitrary probability measures; reason: with a density (no atom at p) Pr[v ≥ p] = 1 − F(p), so the source's formula is the special case
--   - generalization: the SPM offers to every agent whose addition is feasible → the SPM offers only to agents of a set `active`; reason: `active` = all agents is the paper's SPM
--   - encoding: price p_i and probability c_i indexed by step i, agent σ(i) → prices indexed by agent; step t considers agent σ t (σ : Fin n ≃ Fin n); reason: a relabelling through the bijection σ
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, unnumbered, p. 4

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmOffered
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmRevenue
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Revenue formula for sequential posted-price mechanisms: `R^σ_p = Σ_i c_i q_i p_i`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.2, unnumbered, p. 4 (PDF p. 6): "Let ci denote the probability taken over values of
agents σ(1), · · · , σ(i − 1) that the mechanism offers to serve agent i, and let qi = 1 −
Fi(pi). Then the expected revenue of the sequential mechanism, R^σ_p, is given by Σ_i ci qi pi."

For independent values `v_i ∼ μ i`, any set system `J`, any prices, any set of active agents and
any order `σ`, the expected revenue of the SPM is
`Σ_t Pr[offer at step t] · Pr[v_{σ t} ≥ p_{σ t}] · p_{σ t}`.

**Formalization Note.** Prices are indexed by agent and the order maps step `t` to agent `σ t`.
The acceptance probability is `Pr[v ≥ p] = μ([p, ∞))`, which is the paper's `1 − F(p)` when the
distribution has no atom at `p` (always the case in the paper, whose distributions have
densities); the formula is stated for arbitrary probability measures. -/
theorem spm_revenue_formula {n : ℕ} (Feas : Finset (Fin n) → Prop)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n) :
    spmRevenue Feas μ p active σ =
      ∑ t : Fin n, (Measure.pi μ {v | spmOffered Feas p active σ v t}).toReal
        * (μ (σ t) (Set.Ici (p (σ t)))).toReal * p (σ t) := by sorry

end SeqPostedPricing.MatroidSPM
