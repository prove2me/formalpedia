-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_theorem_3_2
-- name    : PosIndexNash.PPADS.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:34:30.273273+00:00
-- url     : https://prove2.me/theorems/69759b7d-5222-4a36-803e-ddd28892b8db
-- title:
--   Theorem 3.2 — Positive-Index Nash belongs to PPADS
-- statement:
--   **Positive-Index Nash belongs to PPADS**: there is a polynomial-time search reduction from Positive-Index Nash to normalized Sink-of-Line,
--   $$\textsc{Positive-Index Nash} \in \mathrm{PPADS}.$$
--   The reduction is required to be correct only on promised (nondegenerate) input games: for every nondegenerate rational game it outputs a normalized Sink-of-Line instance, and every solution of that instance maps back, in polynomial time, to an exact Nash equilibrium of index $+1$.
--
--   This is the membership half of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: games, equilibria and circuits as mathematical objects; "polynomial-time reduction" → binary codes (`RatGame.enc`, `encRatVec`, `encCircuit`) and `CardinalMatching.SearchReduces` (Cook Turing machines; correctness on valid, i.e. nondegenerate, instances and for every answer); reason: standard encoding of the paper's search problems; the promise semantics is that of p. 14.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 18, Theorem 3.2

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_PPADSClass
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexNash

namespace PosIndexNash.PPADS

theorem theorem_3_2 : PositiveIndexNash ∈ PPADSClass := by sorry

end PosIndexNash.PPADS
