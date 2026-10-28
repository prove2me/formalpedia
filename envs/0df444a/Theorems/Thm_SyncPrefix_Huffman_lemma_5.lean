-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_lemma_5
-- name    : SyncPrefix.Huffman.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:11.697036+00:00
-- url     : https://prove2.me/theorems/444ad109-24d2-44fb-9fc4-c95ed272378c
-- title:
--   Lemma 5, p. 6 — a synchronizing strongly acyclic automaton over k letters becomes, in polynomial time, a Huffman decoder over k + 2 letters with the same shortest synchronizing length
-- statement:
--   There is a polynomial-time computable map on encodings of automata with the following property. For every synchronizing strongly acyclic automaton $A$ with $n$ states over an alphabet of size $k$, the map sends the code of $A$ to the code of an automaton $A_H$ such that
--
--   1. $A_H$ is a Huffman decoder over an alphabet of size $k + 2$;
--   2. $A_H$ is synchronizing and $\ell(A_H) = \ell(A)$;
--   3. $n \le n_H \le 2n$, where $n_H$ is the number of states of $A_H$.
--
--   In the paper, $A_H$ adds two letters $b_1, b_2$ and a full binary tree rooted at the sink $f$ of $A$ whose leaves are the states of $A$ without incoming transitions. The lemma moves inapproximability from strongly acyclic automata to Huffman decoders (Corollary 6).
--
--   Differences from the source:
--   - generalization: "there exists a Huffman decoder A_H … with the same length of a shortest synchronizing word" → also n ≤ n_H ≤ 2n; reason: the construction adds fewer than n tree states, and Corollary 6 (iii) needs the bound; dropping the conjunct gives the source's statement.
--   - reading: Huffman decoder → strongly connected, with a state whose set of first-return words is finite; reason: the paper introduces first-return codes for strongly connected automata (p. 3), and the construction produces strongly connected decoders; it is the stronger conclusion.
--   - encoding: "A_H can be constructed in polynomial time" → a polynomial-time computable map f on encodings with f(code(A)) = code(A_H) for every synchronizing strongly acyclic A; reason: Lean convention; f is unconstrained on other inputs.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 6, Lemma 5 (and its proof)

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_CookPvsNP_defs

namespace SyncPrefix.Huffman

/-- Lemma 5 (p. 6): a polynomial-time computable map on encodings sends every synchronizing
strongly acyclic automaton over `k` letters to a Huffman decoder over `k + 2` letters with the
same shortest synchronizing word length and between `n` and `2n` states. -/
theorem lemma_5 :
    ∃ f : List (Option Bool) → List (Option Bool), CookPvsNP.PolyTimeComputable f ∧
      ∀ A : Automaton, StronglyAcyclic A.δ → IsSynchronizing A.δ →
        ∃ AH : Automaton, f A.encode = AH.encode ∧ IsHuffmanDecoder AH.δ ∧ AH.k = A.k + 2 ∧
          IsSynchronizing AH.δ ∧ syncLength AH.δ = syncLength A.δ ∧
            A.n ≤ AH.n ∧ AH.n ≤ 2 * A.n := by sorry

end SyncPrefix.Huffman
