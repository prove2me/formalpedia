-- Prove2me | Theorems.Thm_SparseHistComm_k_subset_prob_bound
-- name    : SparseHistComm.k_subset_prob_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:48.680736+00:00
-- url     : https://prove2.me/theorems/314104e0-7a49-45d0-80be-09339be52cb7
-- title:
--   Proof of Lemma 2 — $k$-subset probability $\binom{d-j}{k-j}/\binom dk \le 1/\lfloor d/k\rfloor^j$ and the union bound $P(|\mathrm{supp}(X) \cap I| \ge j) \le (k/(\tau\lfloor d/k\rfloor))^j$
-- statement:
--   Let $1 \le k \le d$ and $d \ge 2$, and let $X$ be uniform over the $k$-subsets of $\{1,\dots,d\}$.
--
--   1. For $0 \le j \le k$, the probability that $j$ fixed coordinates are all active satisfies
--   $$
--   \frac{\binom{d-j}{k-j}}{\binom dk} = \prod_{\ell=0}^{j-1} \frac{k - \ell}{d - \ell} \ \le\ \Big(\frac kd\Big)^j \ \le\ \frac{1}{\lfloor d/k\rfloor^j}.
--   $$
--   2. For $0 < \tau < 1$, any set $I \subseteq \{1,\dots,d\}$ with $|I| \le k/\tau$ (such as a posterior list $I_i(m,r)$) and $1 \le j \le k$, a union bound over the $j$-subsets of $I$ gives
--   $$
--   P(|\mathrm{supp}(X) \cap I| \ge j) \le \binom{|I|}{j}\frac{\binom{d-j}{k-j}}{\binom dk} \le \frac{|I|^j}{j!}\cdot\frac{1}{\lfloor d/k\rfloor^j} \le \frac{(k/\tau)^j}{j!}\cdot\frac{1}{\lfloor d/k\rfloor^j} \le \Big(\frac{k}{\tau\lfloor d/k\rfloor}\Big)^j.
--   $$
--
--   A fixed short list rarely contains many true active coordinates of a uniformly random $k$-sparse input.
--
--   Differences from the source:
--   - generalization: the posterior list Iᵢ(m, r) → any set I ⊆ [d] with |I| ≤ k/τ; reason: the chain uses only |I| ≤ k/τ ("a fixed list of this size", p.8), and Iᵢ(m, r) satisfies it by the list-size bound, so the page's case is an instance
--   - encoding: ⌊d/k⌋ and P(|supp(X) ∩ I| ≥ j) under the uniform prior → natural-number division d / k, and the number of k-subsets x with |x ∩ I| ≥ j divided by C(d, k); reason: same quantities
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A (proof of Lemma 2), p.15

import Mathlib

namespace SparseHistComm

/-- **Proof of Lemma 2, `k`-subset probability and union bound** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A, p.15). For
`j ≤ k ≤ d`, the probability under the uniform prior that `j` fixed coordinates are all active is
`C(d−j, k−j)/C(d, k) = ∏_{ℓ=0}^{j−1} (k−ℓ)/(d−ℓ) ≤ (k/d)^j ≤ 1/⌊d/k⌋^j`. For a set `I ⊆ [d]` with
`|I| ≤ k/τ` and `1 ≤ j ≤ k`, a union bound over the `j`-subsets of `I` gives
`P(|supp(X) ∩ I| ≥ j) ≤ C(|I|, j)·C(d−j, k−j)/C(d, k) ≤ (|I|^j/j!)·1/⌊d/k⌋^j ≤ ((k/τ)^j/j!)·1/⌊d/k⌋^j ≤ (k/(τ⌊d/k⌋))^j`.

**Formalization Note** `⌊d/k⌋` is natural-number division `d / k`, at least `1` since `k ≤ d`.
The probability of `|supp(X) ∩ I| ≥ j` under the uniform prior on `k`-subsets is the number of
such subsets divided by `C(d, k)`. -/
theorem k_subset_prob_bound (k d : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d) :
    (∀ j : ℕ, j ≤ k →
      ((d - j).choose (k - j) : ℝ) / (d.choose k) = ∏ ℓ ∈ Finset.range j, ((k : ℝ) - ℓ) / (d - ℓ) ∧
      ∏ ℓ ∈ Finset.range j, ((k : ℝ) - ℓ) / (d - ℓ) ≤ ((k : ℝ) / d) ^ j ∧
      ((k : ℝ) / d) ^ j ≤ 1 / ((d / k : ℕ) : ℝ) ^ j) ∧
    (∀ (τ : ℝ), 0 < τ → τ < 1 → ∀ (I : Finset (Fin d)), (I.card : ℝ) ≤ k / τ →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
      (((((Finset.univ : Finset (Fin d)).powersetCard k).filter
          (fun x => j ≤ (x ∩ I).card)).card : ℝ) / (d.choose k)
          ≤ (I.card.choose j : ℝ) * ((d - j).choose (k - j) : ℝ) / (d.choose k) ∧
        (I.card.choose j : ℝ) * ((d - j).choose (k - j) : ℝ) / (d.choose k)
          ≤ (I.card : ℝ) ^ j / j.factorial * (1 / ((d / k : ℕ) : ℝ) ^ j) ∧
        (I.card : ℝ) ^ j / j.factorial * (1 / ((d / k : ℕ) : ℝ) ^ j)
          ≤ (k / τ) ^ j / j.factorial * (1 / ((d / k : ℕ) : ℝ) ^ j) ∧
        (k / τ) ^ j / j.factorial * (1 / ((d / k : ℕ) : ℝ) ^ j)
          ≤ (k / (τ * ((d / k : ℕ) : ℝ))) ^ j)) := by sorry

end SparseHistComm
