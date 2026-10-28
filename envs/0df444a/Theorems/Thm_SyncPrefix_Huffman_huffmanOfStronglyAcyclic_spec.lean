-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_huffmanOfStronglyAcyclic_spec
-- name    : SyncPrefix.Huffman.huffmanOfStronglyAcyclic_spec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T06:19:57.53851+00:00
-- url     : https://prove2.me/theorems/cbd74677-8adf-4dae-aac5-884b9b4cc04e
-- title:
--   Lemma 5 — Combinatorial Correctness of the Huffman Decoder Construction
-- statement:
--   Let $A = (Q, \Sigma, \delta)$ be a complete deterministic automaton that is strongly acyclic and synchronizing, and let $A_H = \mathrm{huffmanOfStronglyAcyclic}(A)$ be the automaton over $k + 2$ letters with at most $2n$ states constructed in the proof of Lemma 5 (Ryzhikov–Szykuła 2018, p. 6). Then:
--
--   $$\mathrm{IsHuffmanDecoder}(A_H.\delta) \;\wedge\; \mathrm{IsSynchronizing}(A_H.\delta) \;\wedge\; \mathrm{syncLength}(A_H.\delta) = \mathrm{syncLength}(A.\delta).$$
--
--   This theorem isolates the combinatorial core of Lemma 5: attaching a delay stem of $n - |S|$ auxiliary states followed by a caterpillar binary tree reaching the source states $S$ of $A$ makes $A_H$ strongly connected with finitely many first-return words at the sink $f$, while preserving the length of the shortest synchronizing word.
-- source:
--   Ryzhikov–Szykuła 2018, Synchronizing Prefix Codes and Huffman’s Algorithm, arXiv:1806.06299v1, p. 6, Lemma 5

import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_SyncPrefix_Huffman_Lemma5Construction

namespace SyncPrefix.Huffman

/-- Combinatorial specification of `huffmanOfStronglyAcyclic` for Lemma 5 (p. 6): for every
synchronizing strongly acyclic automaton `A`, the constructed automaton `huffmanOfStronglyAcyclic A`
is a synchronizing Huffman decoder with the same shortest synchronizing word length as `A`. -/
theorem huffmanOfStronglyAcyclic_spec (A : Automaton)
    (hSA : StronglyAcyclic A.δ) (hSync : IsSynchronizing A.δ) :
    IsHuffmanDecoder (huffmanOfStronglyAcyclic A).δ ∧
      IsSynchronizing (huffmanOfStronglyAcyclic A).δ ∧
      syncLength (huffmanOfStronglyAcyclic A).δ = syncLength A.δ := by sorry

end SyncPrefix.Huffman
