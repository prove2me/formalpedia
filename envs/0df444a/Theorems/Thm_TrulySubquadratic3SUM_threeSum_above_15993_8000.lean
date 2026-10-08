-- Prove2me | Theorems.Thm_TrulySubquadratic3SUM_threeSum_above_15993_8000
-- name    : TrulySubquadratic3SUM.threeSum_above_15993_8000
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T18:12:02.075207+00:00
-- url     : https://prove2.me/theorems/3760a8d6-2452-44c6-8998-403e70dbcd76
-- title:
--   3SUM for every rational exponent above $1.999125$
-- statement:
--   For every rational $r>1.999125=15993/8000$, the following holds. For every fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural constant $b$, and a step bound $T$ that work for every input size $n$ and every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. On $n$ integers of absolute value at most $n^\kappa$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct indices have values summing to zero. Repeated values at distinct positions are allowed, and inputs with fewer than three positions are rejected.
--
--   The time bound is $T(n)=O(n^r)$, expressed by the foundation definition `EndStatement.BigO T r`. The program and constants may depend on $r$ and $\kappa$. This is a consequence of the existing $n^{1.999125+o(1)}$ bound.
-- source:
--   Consequence of the pinned Anthropic formalization, commit e1a4e6508154ea59f030480661590a9fe3018011: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/TimeClaims/Sec3/Theorem21_22.lean#L239-L257 (threeSum_of_uniform_theorem_21a), using the Corollary 26 uniform Exact Triangle bound, delta = 0.00175. This sharpens the rounding of the existing algorithm.

import Mathlib.Data.Rat.Init
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubquadratic3SUM.threeSum_above_15993_8000 (r : ℚ) (hr : (1.999125 : ℚ) < r) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
