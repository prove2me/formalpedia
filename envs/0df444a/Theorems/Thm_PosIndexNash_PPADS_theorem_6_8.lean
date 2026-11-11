-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_theorem_6_8
-- name    : PosIndexNash.PPADS.theorem_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:33:41.846402+00:00
-- url     : https://prove2.me/theorems/e332c86f-6d25-4d89-bb4f-ec64a25ac873
-- title:
--   Theorem 6.8 — PPADS-hardness: Sink-of-Line reduces to Positive-Index Nash, with nondegenerate output games
-- statement:
--   There is a polynomial-time reduction from Sink-of-Line to the problem: given a rational nondegenerate bimatrix game, find a Nash equilibrium of index $+1$. In particular, every output instance of the reduction satisfies the nondegeneracy promise:
--   $$\textsc{Sink-of-Line} \le_p \textsc{Positive-Index Nash}.$$
--   Because the promise is part of validity, the reduction maps every normalized Sink-of-Line instance to a nondegenerate rational game, and maps every index-$+1$ equilibrium of that game back, in polynomial time, to a string $z$ with $P(S(z)) \ne z$.
--
--   Differences from the source:
--   - encoding: games, equilibria and circuits; "polynomial-time reduction" → binary codes (`RatGame.enc`, `encRatVec`, `encCircuit`) and `CardinalMatching.SearchReduces` (Cook Turing machines; the instance map must output valid, i.e. nondegenerate, games; correctness for every answer); reason: standard encoding; "every output instance satisfies the promise" is the validity clause of `SearchReduces`.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 51, Theorem 6.8

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PosIndexNash_PPADS_SinkOfLine
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexNash

namespace PosIndexNash.PPADS

theorem theorem_6_8 : CardinalMatching.SearchReduces SinkOfLine PositiveIndexNash := by sorry

end PosIndexNash.PPADS
