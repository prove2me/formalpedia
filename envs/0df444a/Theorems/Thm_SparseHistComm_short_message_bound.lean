-- Prove2me | Theorems.Thm_SparseHistComm_short_message_bound
-- name    : SparseHistComm.short_message_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:42:32.783955+00:00
-- url     : https://prove2.me/theorems/6e6d0a13-6eb0-49e7-b76b-e0588cac5aeb
-- title:
--   Proof of Lemma 2 — short messages: $P(J_i \ge j, |M_i| < jL \mid R = r) \le 2(2^L k/(\tau\lfloor d/k\rfloor))^j$
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$, $0 < \tau < 1$, let $L > 0$ be a length and $1 \le j \le k$. Then the number of binary strings shorter than $jL$ is
--   $$
--   \sum_{\ell=0}^{\lceil jL\rceil - 1} 2^\ell \ <\ 2^{jL+1},
--   $$
--   and, summing over these strings, for every protocol (either encoder model), every user $i$ and every public realization $r$, under the prior of (16),
--   $$
--   P(J_i \ge j,\ |M_i| < jL \mid R = r) \ \le\ 2\Big(\frac{2^L k}{\tau\lfloor d/k\rfloor}\Big)^j .
--   $$
--
--   Identifying $j$ active coordinates with a message shorter than $jL$ bits is unlikely.
--
--   Differences from the source:
--   - generalization: the (D, δ)-accurate protocol in the proof of Lemma 2 → every protocol; reason: the counting argument uses only the list-size bound and the prior, not accuracy; accurate protocols are an instance
--   - encoding: protocols with any public randomness, channels into {0,1}* → Protocol n d (Ω : Type, measurable PMF (List Bool) channels); reason: same protocols, measurability presupposed by the paper's probabilities
--   - encoding: P(· | R = r) under the prior of (16) → condProb with Bayes' rule posteriors and 0/0 = 0; reason: same quantity
--   - encoding: the number of binary strings shorter than jL → Set.ncard of {m : List Bool | |m| < jL}, equal to ∑_{ℓ < ⌈jL⌉} 2^ℓ; reason: same count
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A (proof of Lemma 2), p.15

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_count
import Definitions.Def_SparseHistComm_condProb
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- **Proof of Lemma 2, short messages** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A, p.15). For a positive length `L` and
`1 ≤ j ≤ k`, the number of binary strings shorter than `jL` is
`∑_{ℓ=0}^{⌈jL⌉−1} 2^ℓ < 2^{jL+1}`, and summing over these strings gives, for every protocol,
user `i` and public realization `r`,
`P(Jᵢ ≥ j, |Mᵢ| < jL | R = r) ≤ 2(2^L k/(τ⌊d/k⌋))^j`.

**Formalization Note** `2^L` and `2^{jL+1}` are real powers; `⌈jL⌉` is `Nat.ceil`; the
conditional probability is `condProb` (prior of Section IV, given `R = r`). -/
theorem short_message_bound (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (L : ℝ) (hL : 0 < L) (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ({m : List Bool | (m.length : ℝ) < j * L}.ncard : ℝ) =
        ∑ ℓ ∈ Finset.range ⌈(j : ℝ) * L⌉₊, (2 : ℝ) ^ ℓ ∧
    ∑ ℓ ∈ Finset.range ⌈(j : ℝ) * L⌉₊, (2 : ℝ) ^ ℓ < (2 : ℝ) ^ ((j : ℝ) * L + 1) ∧
    ∀ (P : Protocol n d) (i : Fin n) (r : P.Ω),
      condProb P k r (fun X m => j ≤ count P k τ i r X m ∧ ((m i).length : ℝ) < j * L) ≤
        ENNReal.ofReal (2 * ((2 : ℝ) ^ L * k / (τ * ((d / k : ℕ) : ℝ))) ^ j) := by sorry

end SparseHistComm
