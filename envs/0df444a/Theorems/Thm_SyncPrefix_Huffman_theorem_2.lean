-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_theorem_2
-- name    : SyncPrefix.Huffman.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:55.838274+00:00
-- url     : https://prove2.me/theorems/d92ccae2-a798-48b0-8420-d21d129d3ef2
-- title:
--   Theorem 2, p. 5 — unless P = NP, Short Sync Word on n-state strongly acyclic automata over alphabets of size n^{1+γ} has no polynomial-time c log n-approximation
-- statement:
--   Assume the Set Cover hardness of [4]: for every $\gamma > 0$ there is $c' > 0$ such that a polynomial-time $c' \log p$-approximation of Set Cover on instances with $|C| \le |X|^{1+\gamma}$, $p = |X|$, implies P = NP.
--
--   Then for every $\gamma > 0$ there is $c > 0$ with the following property. If some polynomial-time algorithm, on every synchronizing strongly acyclic automaton $A$ with $n$ states (for $n$ large enough) over an alphabet of at most $n^{1+\gamma}$ letters, outputs a number $v$ with
--   $$\ell(A) \le v \le c \log n \cdot \ell(A),$$
--   then P = NP.
--
--   It is the first of the paper's logarithmic inapproximability results; Lemma 5 transfers it to Huffman decoders.
--
--   Differences from the source:
--   - reading: "unless P = NP", proved from [4] → the Set Cover hardness of [4] is a hypothesis (`SetCoverHardness`); reason: it is a cited theorem the paper does not prove.
--   - reading: "approximated in polynomial time within a factor of c log n" → value form, an algorithm outputting a number between ℓ(A) and c log n · ℓ(A) on every synchronizing instance of the class with n ≥ n₀; reason: Short Sync Word outputs a length; this is the form of the published Feige definition. [4]'s hardness is read in the same value form.
--   - reading: "over an alphabet of size n^{1+γ}" → at most n^{1+γ} letters; reason: n^{1+γ} is not an integer in general, and the proof produces m < p^{1+γ} letters.
--   - encoding: automata, P and NP → `Automaton` with a unary encoding, `CookPvsNP` Turing machines, natural logarithm; reason: Lean conventions, the base of the logarithm is absorbed in c.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 5, Theorem 2 (and the Set Cover hardness of [4] quoted on p. 5)

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Complexity

namespace SyncPrefix.Huffman

/-- Theorem 2 (p. 5), under the Set Cover hardness of [4]: for every `γ > 0` there is `c > 0`
such that a polynomial-time `c log n`-approximation of Short Sync Word on `n`-state strongly
acyclic automata over alphabets of size at most `n^{1+γ}` implies `P = NP`. -/
theorem theorem_2 (hSC : SetCoverHardness) :
    ∀ γ : ℝ, 0 < γ → ∃ c : ℝ, 0 < c ∧
      (SSWApproxWithin (fun A => StronglyAcyclic A.δ ∧ (A.k : ℝ) ≤ (A.n : ℝ) ^ (1 + γ))
        (fun n => c * Real.log n) → PEqNP) := by sorry

end SyncPrefix.Huffman
