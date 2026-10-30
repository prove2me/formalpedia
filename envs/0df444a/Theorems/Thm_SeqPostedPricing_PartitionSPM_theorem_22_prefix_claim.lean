-- Prove2me | Theorems.Thm_SeqPostedPricing_PartitionSPM_theorem_22_prefix_claim
-- name    : SeqPostedPricing.PartitionSPM.theorem_22_prefix_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:15:59.92821+00:00
-- url     : https://prove2.me/theorems/e1e05b35-bd3a-42fd-b556-101d845d9722
-- title:
--   Theorem 22, proof: the $k$-unit SPM earns $k$ times the 1-item SPM on every prefix
-- statement:
--   Let the agents be indexed in offer order and accept independently with probabilities $q_i \in [0,1]$, where $\sum_i q_i \le k$. In the $k$-unit SPM agent $i$ is offered service with probability $c_i$, the probability that fewer than $k$ of the earlier agents accept. In the corresponding 1-item SPM with acceptance probabilities $q'_i = q_i / k$ it is offered with probability $c'_i = \prod_{l < i}(1 - q_l/k)$. Then for every $j$,
--
--   $$
--   k \sum_{i < j} c'_i\, q'_i \;\le\; \sum_{i < j} c_i\, q_i .
--   $$
--
--   Multiplied by the common price $p \ge 0$ this says that the revenue of the first agents in the $k$-unit case is at least $k$ times the revenue of the same agents in the 1-item case; for the whole set of agents it gives the $k$-unit case of the equal-price bound from the 1-item case.
--
--   **Formalization Note** For $k = 0$ the hypotheses force every $q_i = 0$ and both sides are $0$.
--
--   Differences from the source:
--   - reading: R_{j−1} ≥ k R′_{j−1}, revenues of the k-item and 1-item SPMs → Σ_{i<j} c_i q_i ≥ k Σ_{i<j} c′_i q′_i with c_i = `kOfferProb k q i`, c′_i = Π_{l<i}(1 − q_l/k), q′_i = q_i/k; reason: by the §2.2 formula these are the revenues, whose offer probabilities depend only on the q's
--   - encoding: Σ_{i=1}^{j−1} c_i p q_i ≥ k · Σ_{i=1}^{j−1} c′_i p q_i′ → the same with the common price p ≥ 0 factored out; reason: multiplying by p ≥ 0 preserves the inequality
--   - encoding: for j − 1 ≤ n → for every j : ℕ (prefix of the agents with index < j); reason: a prefix with j > n is the whole set, which the paper's claim covers at j − 1 = n
--   - encoding: agents 1, …, n → `Fin n` with its order; reason: Lean indexing convention; the same instances
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 22, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_kOfferProb

namespace SeqPostedPricing.PartitionSPM

/-- **Prefix claim in the proof of Theorem 22 (revenue-formula form)** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 22,
p. 15 = PDF p. 17): "We assume that for j − 1 ≤ n, the revenue Rj−1 from the first j − 1 items is at
least k times the revenue R′j−1 from the first j − 1 items in the corresponding 1-item case i.e.
Σ_{i=1}^{j−1} ci p qi ≥ k · Σ_{i=1}^{j−1} c′i p qi′. We prove the same for j through two cases."

Agents are indexed in offer order and accept independently with probabilities `q_i ∈ [0, 1]`,
`Σ_i q_i ≤ k`. In the `k`-unit SPM agent `i` is offered with probability `c_i` (fewer than `k`
earlier acceptances, `kOfferProb`); in the 1-item SPM with probabilities `q′_i = q_i/k` it is
offered with probability `c′_i = Π_{l<i} (1 − q_l/k)`. For every prefix of the agents (those of
index `< j`), `k Σ_{i<j} c′_i q′_i ≤ Σ_{i<j} c_i q_i`.

**Formalization Note** Reading 7: the common price `p ≥ 0` is factored out, and the revenues are
written through the §2.2 formula. "For j − 1 ≤ n" ranges over all prefixes; `∀ j : ℕ` covers them
(a prefix with `j ≥ n` is the whole set). At `k = 0` the hypotheses force `q = 0` and both sides are
`0` (Lean's `q / 0 = 0` is never used otherwise). -/
theorem theorem_22_prefix_claim {n : ℕ} (k : ℕ) (q : Fin n → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hsum : ∑ i, q i ≤ k) (j : ℕ) :
    (k : ℝ) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j),
        (∏ l ∈ Finset.univ.filter (· < i), (1 - q l / k)) * (q i / k)
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), kOfferProb k q i * q i := by sorry

end SeqPostedPricing.PartitionSPM
