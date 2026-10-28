-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_huffmanOfStronglyAcyclic_encode_polyTime
-- name    : SyncPrefix.Huffman.huffmanOfStronglyAcyclic_encode_polyTime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T06:20:05.304377+00:00
-- url     : https://prove2.me/theorems/0c7eab20-e2d8-4ae1-b469-d42ff3379c18
-- title:
--   Lemma 5 — Polynomial-Time Computability of the Huffman Decoder Encoding Map
-- statement:
--   There exists a polynomial-time computable function $f : \mathrm{List}(\mathrm{Option\;Bool}) \to \mathrm{List}(\mathrm{Option\;Bool})$ on unary automaton encodings such that for every strongly acyclic synchronizing automaton $A$,
--
--   $$f(\mathrm{encode}(A)) = \mathrm{encode}(\mathrm{huffmanOfStronglyAcyclic}(A)).$$
--
--   This lemma establishes the complexity-theoretic half of Lemma 5 (Ryzhikov–Szykuła 2018, p. 6): identifying the unique sink state $f$ and the source set $S$ of $A$, and emitting the transition table of the $2n$-state Huffman decoder $A_H$ over $k + 2$ letters, can be carried out in polynomial time on multi-tape Turing machines.
-- source:
--   Ryzhikov–Szykuła 2018, Synchronizing Prefix Codes and Huffman’s Algorithm, arXiv:1806.06299v1, p. 6, Lemma 5

import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_SyncPrefix_Huffman_Lemma5Construction
import Definitions.Def_CookPvsNP_defs

namespace SyncPrefix.Huffman

/-- Polynomial-time computability of the encoding transformation in Lemma 5 (p. 6): there is a
polynomial-time computable map `f` on `Option Bool` encodings that sends `A.encode` to
`(huffmanOfStronglyAcyclic A).encode` for every synchronizing strongly acyclic automaton `A`. -/
theorem huffmanOfStronglyAcyclic_encode_polyTime :
    ∃ f : List (Option Bool) → List (Option Bool), CookPvsNP.PolyTimeComputable f ∧
      ∀ A : Automaton, StronglyAcyclic A.δ → IsSynchronizing A.δ →
        f A.encode = (huffmanOfStronglyAcyclic A).encode := by sorry

end SyncPrefix.Huffman
