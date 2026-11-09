-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_circuits_give_admissible
-- name    : SubsetSumPartialMatch.SubsetSum.circuits_give_admissible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:25.921942+00:00
-- url     : https://prove2.me/theorems/a9dde633-c4a2-45d5-9c24-53f46c982752
-- title:
--   Corollary 3.3 — circuits give a partial-match algorithm
-- statement:
--   Every $(l,r)\in K(1/2)$ is an admissible exponent pair.
--
--   This passes from the existence of good EXACT$_\mathbb Z$ circuits to a uniform algorithm for half-stars partial match.
--
--   Differences from the source:
--   - encoding: $A,B$ are sets; time $O(2^{(l+\varepsilon)n}|A|+2^{(r+\varepsilon)n}|B|)$ → duplicate-free lists in any order; time $C(1+2^{(l+\varepsilon)n}|A|+2^{(r+\varepsilon)n}|B|)$ for $n\ge N$; reason: a set must be presented to a machine; the $1$ is the constant overhead of a run and matters only for $A=B=\emptyset$
--   - encoding: bit operations → charged cost of the log-cost RAM of the definition `RAM`; reason: the cost is computed from instructions and operand lengths
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 18, Corollary 3.3

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit

namespace SubsetSumPartialMatch.SubsetSum

/-- Corollary 3.3. Every `(l, r) ∈ K(1/2)` is an admissible exponent pair. -/
theorem circuits_give_admissible {l r : ℝ} (hK : (l, r) ∈ K (1 / 2)) :
    AdmissiblePair l r := by sorry

end SubsetSumPartialMatch.SubsetSum
