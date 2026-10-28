-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_wielandt_code
-- name    : SyncPrefix.Huffman.wielandt_code
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:49.008997+00:00
-- url     : https://prove2.me/theorems/55663de7-e47a-45ce-a426-ffee859b21da
-- title:
--   Proof of Corollary 8, p. 8 (corrected: Z_L has 3·2^{L−1} words, not 2^L) — the Wielandt code is a maximal prefix code whose shortest synchronizing word has length between L² − L + 1 and L²
-- statement:
--   For an integer $L \ge 1$ let
--   $$Z_L = 0\{0,1\}^{L-1} \cup 1\{0,1\}^{L}$$
--   be the set of binary words of length $L$ beginning with $0$ and of length $L+1$ beginning with $1$. Then
--
--   1. $Z_L$ is a maximal prefix code;
--   2. $Z_L$ has exactly $3 \cdot 2^{L-1}$ words;
--   3. its shortest codewords have length $L$ and its longest codewords have length $L + 1$;
--   4. there is a word $w$ of length at most $L^2$ with $\{0,1\}^* w \subseteq Z_L^*$;
--   5. every word $w$ with $\{0,1\}^* w \subseteq Z_L^*$ has length at least $L^2 - L + 1$.
--
--   The minimal automaton of $Z_L^*$ is the Wielandt automaton with $L + 1$ states, and items 4 and 5 are the paper's "synchronizing word of length $\Theta((\log k)^2)$" with $L = \log k$. The code is used in the proof of Corollary 8 to make the alphabet binary.
--
--   Differences from the source:
--   - correction: the proof takes Z = 0{0,1}^{log k−1} ∪ 1{0,1}^{log k} as the image of a bijection from an alphabet of size k = 2^{log k} → |Z_L| = 3·2^{L−1}; reason: for L = 1, Z_1 = {0, 10, 11} has 3 words, not k = 2, so no bijection from a 2-letter alphabet exists; the alphabet must be padded to 3·2^{L−1} letters instead.
--   - reading: "a synchronizing word of length Θ((log k)²)" → the explicit bracket L² − L + 1 ≤ |w| ≤ L² for words w with {0,1}* w ⊆ Z_L*; reason: the lower end is the reset threshold n² − 3n + 3 of the Wielandt automaton ([1]) at n = L + 1, and the upper end makes the Θ explicit.
--   - encoding: the letters 0, 1 and log k → `false`, `true` and L ≥ 1; reason: Lean convention.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8 (second paragraph, the code Z)

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

open Computability

/-- The Wielandt code (p. 8): for `L ≥ 1`, `Z_L = 0{0,1}^{L-1} ∪ 1{0,1}^{L}` is a maximal prefix
code with `3 · 2^{L-1}` words, of lengths `L` and `L + 1`, and the shortest word `w` with
`u w ∈ Z_L∗` for every word `u` has length between `L² − L + 1` and `L²`. -/
theorem wielandt_code (L : ℕ) (hL : 1 ≤ L) :
    IsMaximalPrefixCode (lang (wielandtCode L)) ∧
      (wielandtCode L).card = 3 * 2 ^ (L - 1) ∧
      IsLeast ((fun z : List Bool => z.length) '' (wielandtCode L : Set (List Bool))) L ∧
      IsGreatest ((fun z : List Bool => z.length) '' (wielandtCode L : Set (List Bool))) (L + 1) ∧
      (∃ w : List Bool, w.length ≤ L ^ 2 ∧ ∀ u : List Bool, u ++ w ∈ (lang (wielandtCode L))∗) ∧
      ∀ w : List Bool, (∀ u : List Bool, u ++ w ∈ (lang (wielandtCode L))∗) →
        L ^ 2 - L + 1 ≤ w.length := by sorry

end SyncPrefix.Huffman
