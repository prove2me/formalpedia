-- Prove2me | Theorems.Thm_SeqPostedPricing_PartitionSPM_lemma_20_equal_price_revenue
-- name    : SeqPostedPricing.PartitionSPM.lemma_20_equal_price_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:20.564117+00:00
-- url     : https://prove2.me/theorems/bd2967d1-93b2-4474-bcd9-5ef7f601efcf
-- title:
--   Lemma 20: equalizing the prices does not increase the SPM revenue
-- statement:
--   Let the agents be indexed in offer order, with offer probabilities $c_1 \ge c_2 \ge \cdots \ge c_n$, prices $p_1 \ge p_2 \ge \cdots \ge p_n$ and acceptance probabilities $q_i \ge 0$. Let $\bar p$ be the price with
--
--   $$
--   \sum_i p_i q_i = \bar p \sum_i q_i . \tag{2}
--   $$
--
--   Then
--
--   $$
--   \sum_{i=1}^n c_i \,\bar p\, q_i \le \sum_{i=1}^n c_i \, p_i \, q_i ,
--   $$
--
--   that is, $R^{\mathcal S} \ge R^{\mathcal S}_{eq}$, where $R^{\mathcal S}_{eq}$ is the revenue of the SPM whose prices all equal $\bar p$ and which has the same offer probabilities.
--
--   It reduces the analysis of $\mathcal S$ to an SPM with a single common price.
--
--   Differences from the source:
--   - reading: R^S ≥ R^S_eq (revenues of two SPMs) → Σ_i c_i p̄ q_i ≤ Σ_i c_i p_i q_i; reason: by the §2.2 formula both revenues are Σ_i c_i (price) q_i with the same offer probabilities c_i, which depend only on the q's
--   - generalization: offer probabilities, prices and acceptance probabilities of the SPM S → any non-increasing reals c_i, any non-increasing reals p_i and any q_i ≥ 0; reason: the SPM's c_i are non-increasing and its prices decrease along the order, so it is a special case
--   - encoding: agents 1, …, n → `Fin n` with its order; reason: Lean indexing convention; the same instances
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 20, p. 15 (PDF p. 17); display (2), p. 14 (PDF p. 16)

import Mathlib

namespace SeqPostedPricing.PartitionSPM

/-- **Lemma 20 (revenue-formula form)** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 20, p. 15 = PDF p. 17): "It is always the case
that R^S ≥ R^S_eq." Here (p. 14, display (2)) `p̄` is the price with `Σ_i p_i q_i = p̄ Σ_i q_i`, and
R^S_eq is the revenue of the SPM whose prices all equal `p̄`; the proof writes
`R^S = Σ_{i=1}^n c_i p_i q_i = Σ_{i=1}^n c_i(p̄ q_i + δ_i) = R^S_eq + Σ c_i δ_i ≥ R^S_eq`.

Agents are indexed in offer order. If the offer probabilities `c_i` are non-increasing, the prices
`p_i` are non-increasing, the acceptance probabilities `q_i` are nonnegative and `p̄` satisfies (2),
then `Σ_i c_i p̄ q_i ≤ Σ_i c_i p_i q_i`.

**Formalization Note** Reading 7 of the mission: by the §2.2 revenue formula both revenues are
`Σ_i c_i (price) q_i` with the same offer probabilities `c_i` (they depend only on the `q`'s), so
the lemma is stated about these sums. The proof's three bullets (c descending; δ single-crossing;
Σ δ = 0) follow from the hypotheses. -/
theorem lemma_20_equal_price_revenue {n : ℕ} (c p q : Fin n → ℝ) (pbar : ℝ)
    (hc : Antitone c) (hp : Antitone p) (hq : ∀ i, 0 ≤ q i)
    (h2 : ∑ i, p i * q i = pbar * ∑ i, q i) :
    ∑ i, c i * (pbar * q i) ≤ ∑ i, c i * p i * q i := by sorry

end SeqPostedPricing.PartitionSPM
