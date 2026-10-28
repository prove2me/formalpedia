-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_wielandt_encoding_reduction
-- name    : SyncPrefix.Huffman.wielandt_encoding_reduction
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T06:02:09.885265+00:00
-- url     : https://prove2.me/theorems/f03c1a64-ad75-4972-b38b-8887084ca7fe
-- title:
--   Corollary 8, p. 8 — polynomial-time alphabet reduction via Wielandt code composition
-- statement:
--   In the proof of Corollary 8 (p. 8) of Ryzhikov and Szykuła, a synchronizing Huffman decoder $A_H$ with $n_H \ge 2$ states and $k_H \ge 2$ letters is reduced to a binary ($k_B = 2$) Huffman decoder $A_B$ by choosing $L \ge 1$ with $L \le 2 \log k_H + 2$ and $k_H \le 3 \cdot 2^{L-1} = |Z_L|$, duplicating a letter of $A_H$ to obtain $\delta_Y$ over an alphabet of size $|Z_L|$ (preserving the Huffman decoder property, synchronizability, and shortest synchronizing word length), and reindexing the tree-substitution composition decoder `composeDecoder δY (wielandtCode L) e` into an `Automaton` $A_B$ with $n_H \le n_B \le 6 n_H k_H$ states.
--
--   Furthermore, given any polynomial-time value algorithm $\mathrm{Alg}$ on binary automata encodings, the algorithm $\mathrm{Alg}_H$ that constructs the encoding of $A_B$ from $A_H$, runs $\mathrm{Alg}$, and divides the unary output length by $L$ is polynomial-time computable.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8

import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

theorem wielandt_encoding_reduction (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg_H : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg_H ∧
      ∀ AH : Automaton, IsHuffmanDecoder AH.δ → IsSynchronizing AH.δ → 2 ≤ AH.n → 2 ≤ AH.k →
        ∃ (L : ℕ) (δY : Fin AH.n → Fin (wielandtCode L).card → Fin AH.n)
          (e : Fin (wielandtCode L).card ≃ {z // z ∈ wielandtCode L}) (AB : Automaton),
          1 ≤ L ∧ (L : ℝ) ≤ 2 * Real.log AH.k + 2 ∧
          IsHuffmanDecoder δY ∧ IsSynchronizing δY ∧ syncLength δY = syncLength AH.δ ∧
          AB.k = 2 ∧ AH.n ≤ AB.n ∧ AB.n ≤ 6 * AH.n * AH.k ∧
          (IsHuffmanDecoder (composeDecoder δY (wielandtCode L) e) → IsHuffmanDecoder AB.δ) ∧
          (IsSynchronizing (composeDecoder δY (wielandtCode L) e) → IsSynchronizing AB.δ) ∧
          syncLength AB.δ = syncLength (composeDecoder δY (wielandtCode L) e) ∧
          (Alg_H AH.encode).length = (Alg AB.encode).length / L := by sorry

end SyncPrefix.Huffman
