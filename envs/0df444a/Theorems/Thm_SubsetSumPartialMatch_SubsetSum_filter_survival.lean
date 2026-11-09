-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_filter_survival
-- name    : SubsetSumPartialMatch.SubsetSum.filter_survival
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:30.156908+00:00
-- url     : https://prove2.me/theorems/78598195-6766-4f7c-9da0-83994258e82b
-- title:
--   Lemma 2.6 — filtering and survival of a correct key
-- statement:
--   Under the standing conditions of the reduction, with $p,q$ as defined there and $h$ uniform in $H_p$:
--
--   1. every element of $\mathcal A$ and $\mathcal B$, in every layer, survives with probability less than $2/N_{\mathrm{sum}}$;
--   2. in the good layer of a solution $c$, some correct key survives with probability at least $1/(n/3+3)$.
--
--   The first clause shrinks the lists; the second says the filter keeps a solution alive often enough.
--
--   Differences from the source:
--   - generalization: the lemma sits inside the proof of Theorem 2.2, in the many-sums case, for an admissible pair $(l,r)$ → the numeric conditions $l,r\ge0$, $\xi>0$, $l+r\le1/2-2\xi$ only, with no assumption on $N_{\mathrm{sum}}$; reason: the lemma uses neither admissibility nor the size of $N_{\mathrm{sum}}$; every admissible pair in that case satisfies these conditions
--   - encoding: $s\in\{0,3/n,\dots,1/2\}$ → $w=sn/3\in\{0,\dots,n/6\}$ with $s=3w/n$; reason: the same finite set of layers
--   - encoding: the good layer → any layer with at least $N_{\mathrm{sum}}/(n/3+2)$ distinct correct keys; reason: this is what Lemma 2.5 provides and what the proof uses
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 13, Lemma 2.6

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Reduction

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 2.6. Every element of the conceptual lists survives with probability less than
`2 / N_sum`. In a good layer of a solution `c`, some correct key survives with probability at
least `1 / (n/3 + 3)`. -/
theorem filter_survival {l r ξ : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r) (hξ : 0 < ξ)
    (hlr : l + r ≤ 1 / 2 - 2 * ξ) {n : ℕ} (hn : 6 ∣ n) (hpos : 0 < n)
    (z : Fin n → ℤ) (τ : ℤ) :
    (∀ w ≤ n / 6,
      (∀ a ∈ leftList n (splitPoint n l r (density n w)),
        hashProb (hashModulus z τ)
          (fun α β => Survives (hashModulus z τ) (hashWindow z τ) α β (leftKey z a)) <
            2 / (Nsum z : ℝ)) ∧
      (∀ b ∈ rightList n (splitPoint n l r (density n w)) w,
        hashProb (hashModulus z τ)
          (fun α β => Survives (hashModulus z τ) (hashWindow z τ) α β (rightKey z τ b)) <
            2 / (Nsum z : ℝ))) ∧
    (∀ c : Fin n → Bool, IsSolution z τ c → ∀ w ≤ n / 6,
      (Nsum z : ℝ) / ((n : ℝ) / 3 + 2) ≤
          ((correctKeys z c (splitPoint n l r (density n w)) w).card : ℝ) →
        1 / ((n : ℝ) / 3 + 3) ≤
          hashProb (hashModulus z τ) (fun α β =>
            ∃ k ∈ correctKeys z c (splitPoint n l r (density n w)) w,
              Survives (hashModulus z τ) (hashWindow z τ) α β k)) := by sorry

end SubsetSumPartialMatch.SubsetSum
