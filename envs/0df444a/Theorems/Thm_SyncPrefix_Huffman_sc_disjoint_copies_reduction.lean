-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_sc_disjoint_copies_reduction
-- name    : SyncPrefix.Huffman.sc_disjoint_copies_reduction
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T06:02:13.024345+00:00
-- url     : https://prove2.me/theorems/ebee2117-24ae-486e-a7b5-e7682da267c6
-- title:
--   Padding claim, p. 8 — Set Cover disjoint-copies scaling reduction
-- statement:
--   To establish the Set Cover padding claim on page 8 of Ryzhikov and Szykuła (ensuring the minimum cover size is at least $d \log p$), one takes $p = |X|$ disjoint copies of a coverable Set Cover instance $I = (X, C)$ with $p \ge 1$ points.
--
--   The resulting instance $I'$ is coverable, has $p' = p^2$ points, $m' = p |C|$ subsets, and minimum cover size $\operatorname{minCover}(I') = p \cdot \operatorname{minCover}(I)$ with $\operatorname{minCover}(I) \ge 1$. Moreover, for any polynomial-time algorithm $\mathrm{Alg}$ outputting a unary value on $I'$, the rescaled algorithm $\mathrm{Alg}'$ that constructs the encoding of $I'$, runs $\mathrm{Alg}$, and divides the unary output length by $p$ runs in polynomial time.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8 (Set Cover padding)

import Definitions.Def_SyncPrefix_Huffman_Complexity
open SetCoverThreshold.SetCover

namespace SyncPrefix.Huffman

theorem sc_disjoint_copies_reduction (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg' : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg' ∧
      ∀ I : SCInstance, I.Coverable → 1 ≤ I.n →
        ∃ I' : SCInstance, I'.Coverable ∧ I'.n = I.n ^ 2 ∧
          I'.sets.length = I.n * I.sets.length ∧
          minCover I' = I.n * minCover I ∧
          1 ≤ minCover I ∧
          (Alg' I.encode).length = (Alg I'.encode).length / I.n := by sorry

end SyncPrefix.Huffman
