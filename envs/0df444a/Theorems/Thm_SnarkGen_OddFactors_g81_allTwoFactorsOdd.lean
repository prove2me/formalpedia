-- Prove2me | Theorems.Thm_SnarkGen_OddFactors_g81_allTwoFactorsOdd
-- name    : SnarkGen.OddFactors.g81_allTwoFactorsOdd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:47.936239+00:00
-- url     : https://prove2.me/theorems/d92c90a3-cec0-42be-bce1-52607ca527eb
-- title:
--   Appendix 8.1 — every 2-factor of $G_{8.1}$ consists of odd cycles
-- statement:
--   Let $G_{8.1}$ be the 26-vertex graph of Appendix 8.1. Then every 2-factor of $G_{8.1}$ consists of only odd cycles: for every spanning 2-regular subgraph $F \subseteq G_{8.1}$ and every component $C$ of $F$,
--   $$|V(C)| \ \text{ is odd}.$$
--
--   This is the property named in the heading of Appendix 8.1 and the one at stake in Conjecture 4.11. In a cubic graph the 2-factors are exactly the complements of the perfect matchings; $G_{8.1}$ has 56 perfect matchings, and the statement concerns every one of the corresponding 2-factors.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 29, Appendix 8.1 (heading); p. 11, §4.4, Observation 4.12

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_TwoFactor
import Definitions.Def_SnarkGen_OddFactors_G81

namespace SnarkGen.OddFactors

/-- All 2-factors of the graph `G₈.₁` of Appendix 8.1 (arXiv:1206.6690v3, p. 29) consist of odd
cycles: every connected component of every spanning 2-regular subgraph of `G₈.₁` has an odd number
of vertices. -/
theorem g81_allTwoFactorsOdd : AllTwoFactorsOdd G81 := by sorry

end SnarkGen.OddFactors
