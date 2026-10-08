-- Prove2me | Theorems.Thm_TrulySubquadratic3SUM_threeSum_199913
-- name    : TrulySubquadratic3SUM.threeSum_199913
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T18:12:01.381892+00:00
-- url     : https://prove2.me/theorems/d284346d-62ef-4166-abfe-67b6e6135038
-- title:
--   3SUM in $O(n^{1.99913})$ word-RAM steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural constant $b$, and a step bound $T$ that work for every input size $n$ and every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. On $n$ integers of absolute value at most $n^\kappa$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct indices have values summing to zero. Repeated values at distinct positions are allowed, and inputs with fewer than three positions are rejected.
--
--   The time bound is $T(n)=O(n^{1.99913})$: precisely, there is $K\in\mathbb N$ such that $T(n)^{100000}\le K n^{199913}$ for every $n\ge2$.
-- source:
--   Consequence of the pinned Anthropic formalization, commit e1a4e6508154ea59f030480661590a9fe3018011: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean#L239-L257 (threeSum_of_uniform_theorem_21a), using the Corollary 26 uniform Exact Triangle bound, delta = 0.00175. This sharpens the rounding of the existing algorithm.

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubquadratic3SUM.threeSum_199913 :
    EndStatement.ThreeSum.SolvedInTime 1.99913 := by sorry
