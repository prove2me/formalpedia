-- Prove2me | Theorems.Thm_SnarkGen_OddFactors_g81_egirth
-- name    : SnarkGen.OddFactors.g81_egirth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:52.510554+00:00
-- url     : https://prove2.me/theorems/2ef99882-af20-47bd-84b3-379a4426213c
-- title:
--   Appendix 8.1 — the graph $G_{8.1}$ has girth at least 5
-- statement:
--   Let $G_{8.1}$ be the 26-vertex graph of Appendix 8.1. Then $G_{8.1}$ contains no cycle of length 3 or 4; its girth satisfies
--   $$g(G_{8.1}) \ge 5.$$
--
--   Girth at least 5 is one of the four conditions in the definition of a snark (Section 2), and $G_{8.1}$ must satisfy it to be a counterexample to Conjecture 4.11.
--
--   **Formalization Note** The girth is Mathlib's extended girth `egirth : ℕ∞`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, Section 2 (girth, snark); p. 11, Observation 4.12; p. 29, Appendix 8.1

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_G81

namespace SnarkGen.OddFactors

/-- The graph `G₈.₁` of Appendix 8.1 (arXiv:1206.6690v3, p. 29) has girth at least 5: it has no
cycle of length 3 or 4 (the extended girth `egirth` is at least 5). -/
theorem g81_egirth : 5 ≤ G81.egirth := by sorry

end SnarkGen.OddFactors
