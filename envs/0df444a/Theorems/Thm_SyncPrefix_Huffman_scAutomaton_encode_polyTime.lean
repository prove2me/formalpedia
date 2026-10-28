-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_scAutomaton_encode_polyTime
-- name    : SyncPrefix.Huffman.scAutomaton_encode_polyTime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T06:02:17.805833+00:00
-- url     : https://prove2.me/theorems/34014c45-97ac-4434-a4b7-f152d17b856c
-- title:
--   Theorem 2, p. 5 — polynomial-time computability of the pipe automaton encoding
-- statement:
--   In the proof of Theorem 2 of Ryzhikov and Szykuła, each Set Cover instance $I = (X, C)$ with $p = |X|$ points and $m = |C|$ subsets is mapped to the pipe automaton $\mathcal{A}(I)$ (`scAutomaton I`) with $n = p^2 + 1$ states and $k = m$ letters.
--
--   This lemma states that there is a polynomial-time computable function $f$ on string encodings over `Option Bool` (`CookPvsNP.PolyTimeComputable f`) that maps the encoding `I.encode` of every Set Cover instance $I$ to the encoding `(scAutomaton I).encode` of its pipe automaton.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 5, proof of Theorem 2

import Definitions.Def_SyncPrefix_Huffman_Constructions
open SetCoverThreshold.SetCover

namespace SyncPrefix.Huffman

theorem scAutomaton_encode_polyTime :
    ∃ f : List (Option Bool) → List (Option Bool), CookPvsNP.PolyTimeComputable f ∧
      ∀ I : SCInstance, f I.encode = (scAutomaton I).encode := by sorry

end SyncPrefix.Huffman
