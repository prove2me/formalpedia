-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_theorem_4_2_search_reduction
-- name    : PosIndexNash.PPADS.theorem_4_2_search_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:54:33.425179+00:00
-- url     : https://prove2.me/theorems/b55396f2-1833-49b9-bb8d-b176b6b668d4
-- title:
--   Theorem 4.2 as a search reduction to positive-index exact fixed points
-- statement:
--   Theorem 4.2 gives a polynomial-time search reduction
--   $$\textsc{Sink-of-Line}\le_p\textsc{Positive-Index Fixed Point}.$$
--   The instance map is the rational max-affine circuit construction of Theorem 4.2. Its output satisfies the self-map, regularity, and strictness promise. If a rational fixed point $q$ has index $+1$, the certified decoder of Theorem 4.2 returns an $n$-bit string $z$ with $P(S(z))\ne z$. Correctness holds for every positive-index fixed-point answer, as required by a Levin search reduction.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879, pp. 34–35, proof of Theorem 4.2, especially equations (29)–(30) and the exact-decoding paragraph

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PosIndexNash_PPADS_SinkOfLine
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexFixedPoint

theorem PosIndexNash.PPADS.theorem_4_2_search_reduction :
    CardinalMatching.SearchReduces SinkOfLine PositiveIndexFixedPoint := by sorry
