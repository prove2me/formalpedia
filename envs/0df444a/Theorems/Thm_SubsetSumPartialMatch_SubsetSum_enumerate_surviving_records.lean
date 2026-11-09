-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_enumerate_surviving_records
-- name    : SubsetSumPartialMatch.SubsetSum.enumerate_surviving_records
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:54.235044+00:00
-- url     : https://prove2.me/theorems/5adedac5-4e0d-42a2-9f89-1e5ff878409d
-- title:
--   Lemma 2.7 — enumerate surviving records
-- statement:
--   Under the standing conditions of the reduction, there is one deterministic program which, given the instance, a layer and a hash $h_{\alpha,\beta}$, lists each surviving record of $\mathcal A$ and of $\mathcal B$ exactly once, in time
--   $$2^{o(n)}\bigl(2^{5n/12}+2^{(1/2-\xi/6)n}+N_L+N_R\bigr),$$
--   where $N_L,N_R$ are the numbers of surviving records in $\mathcal A$ and $\mathcal B$. The bound is output-sensitive: the conceptual lists are not enumerated first.
--
--   Differences from the source:
--   - generalization: the lemma sits inside the proof of Theorem 2.2, in the many-sums case, for an admissible pair $(l,r)$ → the numeric conditions $l,r\ge0$, $\xi>0$, $l+r\le1/2-2\xi$ only, with no assumption on $N_{\mathrm{sum}}$; reason: the lemma uses neither admissibility nor the size of $N_{\mathrm{sum}}$; every admissible pair in that case satisfies these conditions
--   - encoding: $s\in\{0,3/n,\dots,1/2\}$ → $w=sn/3\in\{0,\dots,n/6\}$ with $s=3w/n$; reason: the same finite set of layers
--   - encoding: $2^{o(n)}$ → a function $g$ with $g(n)=o(n)$, chosen after the envelope $B$; reason: the source assumes input length $2^{o(n)}$, and its factor depends on that length
--   - encoding: input length $2^{o(n)}$ bits → every envelope $B$ with $\log_2B(n)/n\to0$ and all instances with $L\le B(n)$; reason: this is the quantified form of the promise; no polynomial bound is imposed
--   - encoding: bit operations → charged cost of the log-cost RAM of the definition `RAM`; reason: the cost is computed from instructions and operand lengths
--   - encoding: the algorithm knows $s$, $\ell$, $p$, $q$, $h$ from the surrounding procedure → these are input words; $\ell$ must equal the choice of the reduction; reason: the lemma concerns the listing step alone
--   - generalization: an algorithm for inputs of length $2^{o(n)}$ → one program, chosen before the envelope $B$, for all envelopes; reason: the source's procedure does not read an envelope; fixing $B$ gives the source case
--   - encoding: the surviving records are listed → the output is the two list lengths followed by the vectors of the lists, coordinate by coordinate, each record exactly once; the instance is given as machine words; reason: machine presentation of the same data
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 13, Lemma 2.7

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Reduction

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 2.7. One deterministic program lists the surviving records of every layer and every
hash, without listing the conceptual lists, in time
`2^{o(n)} (2^{5n/12} + 2^{(1/2-ξ/6)n} + N_L + N_R)`. The `o(n)` depends on the input-length
envelope `B` only. -/
theorem enumerate_surviving_records {l r ξ : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r) (hξ : 0 < ξ)
    (hlr : l + r ≤ 1 / 2 - 2 * ξ) :
    ∃ P : Program, Deterministic P ∧ ∀ B : ℕ → ℕ, IsSubexpEnvelope B →
      ∃ g : ℕ → ℝ, Asymptotics.IsLittleO Filter.atTop g (fun n : ℕ => (n : ℝ)) ∧
        ∀ (n : ℕ), 6 ∣ n → 0 < n → ∀ (z : Fin n → ℤ) (τ : ℤ), instanceBits z τ ≤ B n →
          ∀ w ≤ n / 6, ∀ α < hashModulus z τ, ∀ β < hashModulus z τ,
            ∃ LA LB : List (Fin n → ℤ),
              Enumerates LA (survivingLeft z τ (splitPoint n l r (density n w)) α β) ∧
              Enumerates LB (survivingRight z τ (splitPoint n l r (density n w)) w α β) ∧
              Outputs P blankTape
                (filterWords z τ w (splitPoint n l r (density n w)) α β) (recordWords LA LB) ∧
              CostWithin P blankTape (filterWords z τ w (splitPoint n l r (density n w)) α β)
                ((2 : ℝ) ^ g n * ((2 : ℝ) ^ (5 * (n : ℝ) / 12) +
                  (2 : ℝ) ^ ((1 / 2 - ξ / 6) * (n : ℝ)) + LA.length + LB.length)) := by sorry

end SubsetSumPartialMatch.SubsetSum
