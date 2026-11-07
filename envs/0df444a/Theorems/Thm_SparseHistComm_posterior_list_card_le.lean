-- Prove2me | Theorems.Thm_SparseHistComm_posterior_list_card_le
-- name    : SparseHistComm.posterior_list_card_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:23.235184+00:00
-- url     : https://prove2.me/theorems/15d43c8a-b00e-478d-8d92-5f8cc5db7b46
-- title:
--   Proof of Lemma 2 — list size $\tau|I_i(m,r)| \le \sum_{a \in I_i} P(X_i(a)=1 \mid m, r) \le k$, so $|I_i(m,r)| \le k/\tau$
-- statement:
--   Let $n \ge 1$, $1 \le k \le d$, $d \ge 2$, $0 < \tau < 1$. For any protocol, user $i$, public realization $R = r$ and binary string $m$, the posterior list $I_i(m,r)$ satisfies
--   $$
--   \tau |I_i(m,r)| \ \le \sum_{a \in I_i(m,r)} P(X_i(a) = 1 \mid M_i = m, R = r) \ \le\ \sum_{a=1}^d P(X_i(a) = 1 \mid M_i = m, R = r) \ \le\ k ,
--   $$
--   with $\sum_{a=1}^d P(X_i(a) = 1 \mid M_i = m, R = r) = k$ whenever $P(M_i = m \mid R = r) > 0$. Hence $|I_i(m,r)| \le k/\tau$.
--
--   Every posterior list is short: it is the set the short-message bound counts over.
--
--   Differences from the source:
--   - generalization: the (D, δ)-accurate protocol in the proof of Lemma 2 → every protocol; reason: the chain uses only Bayes' rule and |Xᵢ| = k, not accuracy; accurate protocols are an instance
--   - encoding: ∑ₐ P(Xᵢ(a) = 1 | Mᵢ = m, R = r) = k → ≤ k for every m, and = k when P(Mᵢ = m | R = r) > 0; reason: the posterior is undefined for a message of conditional probability zero, whose list p.15 allows to be empty (0/0 = 0)
--   - encoding: protocols with any public randomness, channels into {0,1}* → Protocol n d (Ω : Type, measurable PMF (List Bool) channels); reason: same protocols, measurability presupposed by the paper's probabilities
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A (proof of Lemma 2), p.15

import Mathlib
import Definitions.Def_SparseHistComm_Protocol
import Definitions.Def_SparseHistComm_msgMass
import Definitions.Def_SparseHistComm_post
import Definitions.Def_SparseHistComm_postList

namespace SparseHistComm

/-- **Proof of Lemma 2, list size** (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Appendix B-A, p.15). For every user `i`, public
realization `r` and binary string `m`,
`τ|Iᵢ(m, r)| ≤ ∑_{a ∈ Iᵢ(m,r)} P(Xᵢ(a) = 1 | Mᵢ = m, R = r) ≤ ∑_{a=1}^d P(Xᵢ(a) = 1 | Mᵢ = m, R = r) ≤ k`,
with equality `= k` in the last step when `m` has positive conditional probability; hence
`|Iᵢ(m, r)| ≤ k/τ`.

**Formalization Note** The page prints `= k` for the last sum. With the convention that a
message of conditional probability zero has posterior `0` (so its list is empty, as p.15
allows), the sum is `0` for such messages; the statement gives `≤ k` always and `= k` when
`P(Mᵢ = m | R = r) > 0`. -/
theorem posterior_list_card_le (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 ≤ d)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (P : Protocol n d) (i : Fin n) (r : P.Ω) (m : List Bool) :
    τ * (postList P k τ i r m).card ≤ ∑ a ∈ postList P k τ i r m, post P k i r m a ∧
    ∑ a ∈ postList P k τ i r m, post P k i r m a ≤ ∑ a, post P k i r m a ∧
    ∑ a, post P k i r m a ≤ k ∧
    (0 < msgMass P k i r m → ∑ a, post P k i r m a = k) ∧
    ((postList P k τ i r m).card : ℝ) ≤ k / τ := by sorry

end SparseHistComm
