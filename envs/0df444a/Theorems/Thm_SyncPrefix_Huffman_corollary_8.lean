-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_corollary_8
-- name    : SyncPrefix.Huffman.corollary_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:04.950979+00:00
-- url     : https://prove2.me/theorems/71fc1f4a-6dbc-49b7-88dc-fe4fcef971ad
-- title:
--   Corollary 8, p. 8 — unless P = NP, Short Sync Word on binary n-state Huffman decoders has no polynomial-time c log n-approximation
-- statement:
--   Assume the Set Cover hardness of [4]: for every $\gamma > 0$ there is $c' > 0$ such that a polynomial-time $c' \log p$-approximation of Set Cover on instances with $|C| \le |X|^{1+\gamma}$, $p = |X|$, implies P = NP.
--
--   Then there is a constant $c > 0$ with the following property. If some polynomial-time algorithm, on every synchronizing Huffman decoder $A$ over the binary alphabet $\{0, 1\}$ with $n$ states (for $n$ large enough), outputs a number $v$ with
--   $$\ell(A) \le v \le c \log n \cdot \ell(A),$$
--   where $\ell(A)$ is the length of a shortest synchronizing word of $A$, then P = NP.
--
--   A Huffman decoder is a strongly connected complete automaton with a state whose first-return words form a finite (maximal prefix) code; a synchronizing word lets the decoder recover from transmission errors. The corollary says that, unless P = NP, the length of a shortest such word cannot be approximated within a logarithmic factor even for binary decoders.
--
--   Differences from the source:
--   - reading: "unless P = NP", proved from [4] → the Set Cover hardness of [4] (p. 5) is a hypothesis (`SetCoverHardness`); reason: it is a cited theorem the paper does not prove.
--   - reading: "approximated in polynomial time within a factor of c log n" → value form, an algorithm outputting a number between ℓ(A) and c log n · ℓ(A) on every synchronizing binary Huffman decoder with n ≥ n₀ states; reason: Short Sync Word outputs a length; this is the form of the published Feige definition; [4]'s hardness is read in the same value form.
--   - reading: Huffman decoder → strongly connected, with a state whose set of first-return words is finite; reason: the paper's setting (p. 3); a smaller class makes the hardness stronger.
--   - encoding: binary n-state automata, P and NP → `Automaton` with k = 2 and a unary encoding, `CookPvsNP` Turing machines, natural logarithm; reason: Lean conventions; the base of the logarithm is absorbed in c.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, Corollary 8

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Complexity

namespace SyncPrefix.Huffman

/-- Corollary 8 (p. 8), under the Set Cover hardness of [4]: there is `c > 0` such that a
polynomial-time `c log n`-approximation of Short Sync Word on binary `n`-state Huffman decoders
implies `P = NP`. -/
theorem corollary_8 (hSC : SetCoverHardness) :
    ∃ c : ℝ, 0 < c ∧
      (SSWApproxWithin (fun A => A.k = 2 ∧ IsHuffmanDecoder A.δ) (fun n => c * Real.log n) →
        PEqNP) := by sorry

end SyncPrefix.Huffman
