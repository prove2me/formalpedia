-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_scDisjointCopies_encode_polyTime
-- name    : SyncPrefix.Huffman.scDisjointCopies_encode_polyTime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T07:31:59.153722+00:00
-- url     : https://prove2.me/theorems/9d1f7823-be2b-4cc9-a815-28a5cc8eb2c4
-- title:
--   Polynomial-time encoding and output rescaling for disjoint Set Cover copies
-- statement:
--   Let $I = ([n], \mathcal{S})$ be a coverable Set Cover instance with $n \ge 1$, and let $I' = \mathrm{scDisjointCopies}(I)$ be the Set Cover instance formed by taking $n$ disjoint copies of $I$ over the universe $[n^2]$. Suppose $\mathrm{Alg} : \{0, 1, \bot\}^* \to \{1\}^*$ is a polynomial-time algorithm operating on encoded Set Cover instances.
--
--   Then there exists a polynomial-time algorithm $\mathrm{Alg}' : \{0, 1, \bot\}^* \to \{1\}^*$ such that for every coverable Set Cover instance $I$ with $n \ge 1$,
--
--   $$
--   |\mathrm{Alg}'(\mathrm{encode}(I))| = \left\lfloor \frac{|\mathrm{Alg}(\mathrm{encode}(\mathrm{scDisjointCopies}(I)))|}{n} \right\rfloor.
--   $$
--
--   This lemma isolates the polynomial-time Turing-machine transcoding and unary output-length division step in the Set Cover padding reduction used before Corollary 8.
--
--   **Formalization Note** Algorithms producing natural-number value estimates in unary are represented as functions `List (Option Bool) → List Unit`, where the output value is `(Alg w).length`.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8 (Set Cover padding)

import Definitions.Def_SyncPrefix_Huffman_DisjointCopies
import Definitions.Def_CookPvsNP_defs

open SetCoverThreshold.SetCover

namespace SyncPrefix.Huffman

theorem scDisjointCopies_encode_polyTime (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg' : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg' ∧
      ∀ I : SCInstance, I.Coverable → 1 ≤ I.n →
        (Alg' I.encode).length = (Alg (scDisjointCopies I).encode).length / I.n := by sorry

end SyncPrefix.Huffman
