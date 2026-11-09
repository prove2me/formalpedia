-- Prove2me | Theorems.Thm_SignRankMargin_OREquality_theorem_1
-- name    : SignRankMargin.OREquality.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:42:03.119798+00:00
-- url     : https://prove2.me/theorems/6834221c-99a2-44ff-9811-01cca3a3b563
-- title:
--   Theorem 1 — exponential sign-rank bounds for OR of equalities
-- statement:
--   Let $k,n\ge1$ be integers. Rows and columns of $\operatorname{orEquality}(k,n)$ are all $k$-tuples of $n$-bit strings, and an entry is one exactly when some coordinate pair is equal. Then
--
--   $$
--   \operatorname{signRank}(\operatorname{orEquality}(k,n))<2^{k+1},
--   $$
--
--   and, whenever $n\ge10k2^k$,
--
--   $$
--   2^k\le\operatorname{signRank}(\operatorname{orEquality}(k,n)).
--   $$
--
--   Thus the upper bound holds for every positive bit length, and both inequalities hold together at the stated threshold with the exact constant ten. The rank is the minimum ordinary real rank over every strict realization. This goal records the paper's exponential bounds for the complete equality composition.
--
--   Differences from the source:
--   - encoding: n-bit strings and k coordinates, with upper bound for every n ≥ 1 and both bounds for n ≥ 10k2^k → alphabet Fin (2^n) and coordinates Fin k; conjunction of the all-positive-n upper bound with the threshold-conditional lower bound; reason: relabels bit strings bijectively and expresses both source clauses without imposing the threshold on the upper bound
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Theorem 1, p. 2; repeated statement and proof p. 13

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_SignRankMargin_OREquality_Composition

namespace SignRankMargin.OREquality

/-- Theorem 1, p.2 (proof p.13): the upper bound is unconditional in positive n;
only the lower bound requires the threshold 10*k*2^k. -/
theorem theorem_1 (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    signRank (orEquality k n) < 2 ^ (k + 1) ∧
    (10 * k * 2 ^ k ≤ n → 2 ^ k ≤ signRank (orEquality k n)) := by sorry

end SignRankMargin.OREquality
