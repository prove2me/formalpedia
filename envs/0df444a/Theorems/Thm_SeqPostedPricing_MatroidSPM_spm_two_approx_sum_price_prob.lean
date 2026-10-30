-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_spm_two_approx_sum_price_prob
-- name    : SeqPostedPricing.MatroidSPM.spm_two_approx_sum_price_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:45:17.397+00:00
-- url     : https://prove2.me/theorems/6bca3d01-2d67-4c6b-af5e-b327718ac9f6
-- title:
--   Proof of Thm 5: the SPM earns at least $\tfrac12\sum_ip_iq_i$
-- statement:
--   Let $\mathcal J$ be a matroid, let the values be independent, $v_i\sim\mu_i$ (any probability distributions), and run the SPM on a set $\mathcal A$ of agents, with prices nonnegative on $\mathcal A$ and non-increasing along the order $\sigma$. Let $q_i=\Pr[v_i\ge p_i]$. If
--
--   $$
--   \sum_{i\in T\cap\mathcal A}q_i\le\mathrm{rank}(T)\quad\text{for every }T\subseteq[n],
--   $$
--
--   then
--
--   $$
--   \sum_{i\in\mathcal A}p_i\,q_i\ \le\ 2\,\mathcal R^\sigma_{\mathbf p}.
--   $$
--
--   Combined with Lemma 2 this gives Theorem 5.
--
--   Differences from the source:
--   - generalization: the mechanism S: q_i = q_i^M of Myerson's mechanism, p_i = F_i^{−1}(1 − q_i), regular distributions → any probability measures, any set 𝒜 of agents offered to, prices ≥ 0 on 𝒜 and non-increasing along σ, acceptance probabilities q_i = Pr[v_i ≥ p_i] with the rank bound on 𝒜; reason: for S the rank bound holds by rank_bound and accept_prob_eq_quantile, and the prices are ≥ 0 because an optimal mechanism serves an agent only where its virtual value is ≥ 0 and v ≥ φ(v); the proof uses p^ℓ ≥ 0
--   - encoding: Σ_i p_i q_i over all agents → Σ over the agents 𝒜 offered to; reason: in S the agents not offered have q_i = 0
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 5, pp. 6–7

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsMatroid
import Definitions.Def_SeqPostedPricing_MatroidSPM_rank
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmRevenue
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsDecreasingOrder
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **The SPM earns at least half of `Σ_i p_i q_i`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4.1, proof of Theorem 5, p. 6 (PDF p. 8): "We show that the mechanism S obtains an
expected revenue of at least 1/2 Σ_i pi qi."; closing the proof, p. 7 (PDF p. 9): "Therefore,
E[revenue lost] ≤ Σ_S Σ_{j∈S} p^j · Pr[S is served] = R^σ_p, and so it follows that
Σ_i pi qi ≤ 2R^σ_p."

Let `J` be a matroid, values independent with `v_i ∼ μ i`, and let the SPM make offers to the
agents of `active`, at prices that are nonnegative on `active` and non-increasing along `σ`.
Write `q_i = Pr[v_i ≥ p_i]` for the acceptance probabilities. If `Σ_{i∈T∩active} q_i ≤ rank(T)`
for every set `T`, then

`Σ_{i∈active} p_i q_i ≤ 2 R^σ_p`.

**Formalization Note.** Stated for arbitrary probability measures (atoms allowed) and arbitrary
prices with the rank bound; for the mechanism `S` of §4 the hypotheses are supplied by
`rank_bound` and `accept_prob_eq_quantile`. -/
theorem spm_two_approx_sum_price_prob {n : ℕ} (Feas : Finset (Fin n) → Prop)
    (hmat : IsMatroid Feas) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (p : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n)
    (hσ : IsDecreasingOrder p active σ) (hp0 : ∀ i ∈ active, 0 ≤ p i)
    (hrank : ∀ T : Finset (Fin n),
      ∑ i ∈ T ∩ active, (μ i (Set.Ici (p i))).toReal ≤ (rank Feas T : ℝ)) :
    ∑ i ∈ active, p i * (μ i (Set.Ici (p i))).toReal ≤
      2 * spmRevenue Feas μ p active σ := by sorry

end SeqPostedPricing.MatroidSPM
