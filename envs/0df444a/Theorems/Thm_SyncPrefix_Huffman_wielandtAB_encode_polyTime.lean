-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_wielandtAB_encode_polyTime
-- name    : SyncPrefix.Huffman.wielandtAB_encode_polyTime
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T07:25:08.124239+00:00
-- url     : https://prove2.me/theorems/9a368d7f-c9f0-495c-9116-e1e70cc81621
-- title:
--   Corollary 8 (p. 8) — polynomial-time encoding and output rescaling for $A_B$
-- statement:
--   This lemma isolates the polynomial-time encoding and output-length rescaling step in the proof of Corollary 8 (Ryzhikov and Szykuła, 2018, p. 8).
--
--   Let $\mathrm{Alg}$ be a polynomial-time algorithm taking encodings of binary automata to unary outputs in $\mathrm{List\ Unit}$. For any complete deterministic automaton $A_H$ with $n \ge 2$ states and $k \ge 2$ input letters that is a synchronizing Huffman decoder, let $L = \lfloor \log_2(k - 1) \rfloor + 1$ be the Wielandt code parameter and let $A_B = \mathrm{wielandtAB}(A_H)$ be the binary tree-substitution decoder automaton over the Wielandt code $Z_L$. Then there exists a polynomial-time algorithm $\mathrm{Alg}_H$ such that
--
--   $$
--   |\mathrm{Alg}_H(\mathrm{encode}(A_H))| = \left\lfloor \frac{|\mathrm{Alg}(\mathrm{encode}(A_B))|}{L} \right\rfloor.
--   $$
--
--   Combined with the combinatorial and synchronization bounds for $A_B$, this transfers any polynomial-time logarithmic-factor approximation of Short Sync Word on binary Huffman decoders to general Huffman decoders.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8

import Definitions.Def_SyncPrefix_Huffman_WielandtReduction
import Definitions.Def_CookPvsNP_defs

namespace SyncPrefix.Huffman

theorem wielandtAB_encode_polyTime (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg_H : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg_H ∧
      ∀ AH : Automaton, IsHuffmanDecoder AH.δ → IsSynchronizing AH.δ → 2 ≤ AH.n → 2 ≤ AH.k →
        (Alg_H AH.encode).length = (Alg (wielandtAB AH).encode).length / wielandtL AH.k := by sorry

end SyncPrefix.Huffman
