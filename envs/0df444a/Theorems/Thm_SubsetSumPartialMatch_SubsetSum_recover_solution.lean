-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_recover_solution
-- name    : SubsetSumPartialMatch.SubsetSum.recover_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:54.425575+00:00
-- url     : https://prove2.me/theorems/a9bd0f40-200c-4c5d-944a-038fac715f89
-- title:
--   Lemma 2.8 — recover a solution from surviving records
-- statement:
--   Let $(l,r)$ be an admissible exponent pair with $l+r\le1/2-2\xi$, $\xi>0$, and let $\varepsilon>0$. There is one deterministic program which, given the surviving records of a layer, finds a solution among the pairs of surviving records, or correctly reports that none exists, in time
--   $$2^{o(n)}\,\mathrm{cost}(N_L,N_R).$$
--   A pair of records $(a,b)$ forms a solution when the two complete integer keys agree, $a\cdot z=\tau-b\cdot z$, and $a+b\in\{0,1\}^n$; a hash collision is not a solution. The output is the witness $a+b$ itself.
--
--   Differences from the source:
--   - generalization: the lemma sits in the many-sums case of the proof of Theorem 2.2 → no assumption on $N_{\mathrm{sum}}$; reason: the lemma does not use the case assumption; that case is included
--   - encoding: $s\in\{0,3/n,\dots,1/2\}$ → $w=sn/3\in\{0,\dots,n/6\}$ with $s=3w/n$; reason: the same finite set of layers
--   - encoding: $2^{o(n)}$ → a function $g$ with $g(n)=o(n)$, chosen after the envelope $B$; reason: the source assumes input length $2^{o(n)}$, and its factor depends on that length
--   - encoding: input length $2^{o(n)}$ bits → every envelope $B$ with $\log_2B(n)/n\to0$ and all instances with $L\le B(n)$; reason: this is the quantified form of the promise; no polynomial bound is imposed
--   - encoding: bit operations → charged cost of the log-cost RAM of the definition `RAM`; reason: the cost is computed from instructions and operand lengths
--   - encoding: time $2^{o(n)}\mathrm{cost}(N_L,N_R)$ → time $2^{g(n)}(1+\mathrm{cost}(N_L,N_R))$; reason: the $1$ is the constant overhead of a run and matters only for $N_L=N_R=0$
--   - generalization: an algorithm for inputs of length $2^{o(n)}$ → one program, chosen before the envelope $B$, for all envelopes; reason: the source's procedure does not read an envelope; fixing $B$ gives the source case
--   - encoding: the surviving records are given; a solution is found → the input is the instance, $w$, $\ell$, then the two duplicate-free lists of records as machine words; the output is the word $1$ followed by the bits of the witness, or the word $0$; reason: machine presentation of the same data
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 14, Lemma 2.8

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Reduction
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_PartialMatch

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 2.8. One deterministic program, given the surviving records of a layer, finds a solution
among the pairs of surviving records or correctly reports that none exists, in time
`2^{o(n)} (1 + cost(N_L, N_R))`. -/
theorem recover_solution {l r ξ ε : ℝ} (hadm : AdmissiblePair l r) (hξ : 0 < ξ)
    (hlr : l + r ≤ 1 / 2 - 2 * ξ) (hε : 0 < ε) :
    ∃ Q : Program, Deterministic Q ∧ ∀ B : ℕ → ℕ, IsSubexpEnvelope B →
      ∃ g : ℕ → ℝ, Asymptotics.IsLittleO Filter.atTop g (fun n : ℕ => (n : ℝ)) ∧
        ∀ (n : ℕ), 6 ∣ n → 0 < n → ∀ (z : Fin n → ℤ) (τ : ℤ), instanceBits z τ ≤ B n →
          ∀ w ≤ n / 6, ∀ α < hashModulus z τ, ∀ β < hashModulus z τ,
            ∀ LA LB : List (Fin n → ℤ),
              Enumerates LA (survivingLeft z τ (splitPoint n l r (density n w)) α β) →
              Enumerates LB (survivingRight z τ (splitPoint n l r (density n w)) w α β) →
              ((∃ a ∈ LA, ∃ b ∈ LB, ∃ c, PairFormsSolution z τ a b c ∧
                  Outputs Q blankTape
                    (matchWords z τ w (splitPoint n l r (density n w)) LA LB) (solutionWords c)) ∨
                ((¬ ∃ a ∈ LA, ∃ b ∈ LB, ∃ c, PairFormsSolution z τ a b c) ∧
                  Outputs Q blankTape
                    (matchWords z τ w (splitPoint n l r (density n w)) LA LB) noSolutionWords)) ∧
              CostWithin Q blankTape (matchWords z τ w (splitPoint n l r (density n w)) LA LB)
                ((2 : ℝ) ^ g n *
                  (1 + pmCost n l r ε (density n w) (LA.length : ℝ) (LB.length : ℝ))) := by sorry

end SubsetSumPartialMatch.SubsetSum
