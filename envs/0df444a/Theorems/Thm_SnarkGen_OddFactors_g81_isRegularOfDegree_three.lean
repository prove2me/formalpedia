-- Prove2me | Theorems.Thm_SnarkGen_OddFactors_g81_isRegularOfDegree_three
-- name    : SnarkGen.OddFactors.g81_isRegularOfDegree_three
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:57.894999+00:00
-- url     : https://prove2.me/theorems/106e8ad9-3dca-4d6e-a3c7-ef9358060d18
-- title:
--   Appendix 8.1 — the graph $G_{8.1}$ is cubic
-- statement:
--   Let $G_{8.1}$ be the 26-vertex graph of Appendix 8.1. Then $G_{8.1}$ is cubic:
--   $$\deg_{G_{8.1}}(v) = 3 \quad \text{for every vertex } v.$$
--
--   Being cubic is the first of the properties that make $G_{8.1}$ a snark; it is asserted in the heading of Appendix 8.1.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 29, Appendix 8.1 (heading: A cubic graph where all 2-factors only consist of odd cycles)

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_G81

namespace SnarkGen.OddFactors

/-- The graph `G₈.₁` of Appendix 8.1 (arXiv:1206.6690v3, p. 29) is cubic: every vertex has
exactly three neighbours. -/
theorem g81_isRegularOfDegree_three : G81.IsRegularOfDegree 3 := by sorry

end SnarkGen.OddFactors
