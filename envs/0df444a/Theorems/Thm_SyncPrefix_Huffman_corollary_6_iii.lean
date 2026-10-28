-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_corollary_6_iii
-- name    : SyncPrefix.Huffman.corollary_6_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:02.830345+00:00
-- url     : https://prove2.me/theorems/632e09cb-4083-49fb-bbd5-244a9e85a9d0
-- title:
--   Corollary 6 (iii), p. 6 — unless P = NP, Short Sync Word on Huffman decoders over alphabets of size n^{1+γ} has no polynomial-time c log n-approximation
-- statement:
--   Assume the Set Cover hardness of [4] (for every $\gamma > 0$ there is $c' > 0$ such that a polynomial-time $c' \log p$-approximation of Set Cover on instances with $|C| \le |X|^{1+\gamma}$ implies P = NP).
--
--   Then for every $\gamma > 0$ there is $c > 0$ with the following property. If some polynomial-time algorithm, on every synchronizing Huffman decoder $A$ with $n$ states (for $n$ large enough) over an alphabet of at most $n^{1+\gamma}$ letters, outputs a number $v$ with
--   $$\ell(A) \le v \le c \log n \cdot \ell(A),$$
--   then P = NP.
--
--   It is the starting point of the proof of Corollary 8, which then reduces the alphabet to two letters.
--
--   Differences from the source:
--   - reading: "unless P = NP", proved from Theorem 2 and hence from [4] → the Set Cover hardness of [4] is a hypothesis (`SetCoverHardness`); reason: it is a cited theorem the paper does not prove.
--   - reading: "approximated in polynomial time within a factor of c log n" → value form with a threshold n₀, as in Theorem 2; reason: Short Sync Word outputs a length; [4]'s hardness is read in the same value form.
--   - reading: "over an alphabet of size n^{1+γ}" → at most n^{1+γ} letters; reason: n^{1+γ} is not an integer in general, and the proof produces fewer letters.
--   - reading: Huffman decoder → strongly connected, with a state whose set of first-return words is finite; reason: the paper's setting (p. 3); a smaller class makes the hardness stronger.
--   - encoding: automata, P and NP → `Automaton` with a unary encoding, `CookPvsNP` Turing machines, natural logarithm; reason: Lean conventions.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 6, Corollary 6 (iii)

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Complexity

namespace SyncPrefix.Huffman

/-- Corollary 6 (iii) (p. 6), under the Set Cover hardness of [4]: for every `γ > 0` there is
`c > 0` such that a polynomial-time `c log n`-approximation of Short Sync Word on `n`-state
Huffman decoders over alphabets of size at most `n^{1+γ}` implies `P = NP`. -/
theorem corollary_6_iii (hSC : SetCoverHardness) :
    ∀ γ : ℝ, 0 < γ → ∃ c : ℝ, 0 < c ∧
      (SSWApproxWithin (fun A => IsHuffmanDecoder A.δ ∧ (A.k : ℝ) ≤ (A.n : ℝ) ^ (1 + γ))
        (fun n => c * Real.log n) → PEqNP) := by sorry

end SyncPrefix.Huffman
