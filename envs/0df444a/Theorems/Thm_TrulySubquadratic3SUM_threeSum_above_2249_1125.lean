-- Prove2me | Theorems.Thm_TrulySubquadratic3SUM_threeSum_above_2249_1125
-- name    : TrulySubquadratic3SUM.threeSum_above_2249_1125
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T18:42:31.62103+00:00
-- url     : https://prove2.me/theorems/a400114c-d8eb-4993-a17d-790317d4ae49
-- title:
--   3SUM for every rational exponent above $2249 / 1125$
-- statement:
--   For every rational $r>2249/1125$, the following holds. For every fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural constant $b$, and a step bound $T$ that work for every input size $n$ and every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. On $n$ integers of absolute value at most $n^\kappa$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct indices have values summing to zero. Repeated values at distinct positions are allowed, and inputs with fewer than three positions are rejected.
--
--   The time bound is $T(n)=O(n^r)$, expressed by the foundation definition `EndStatement.BigO T r`. The program and constants may depend on $r$ and $\kappa$. This is a consequence of the refined $n^{2249/1125+o(1)}$ bound.
-- source:
--   Parameter refinement of Alman and Vassilevska Williams (2026), derived from Anthropic formal-math commit e1a4e6508154ea59f030480661590a9fe3018011. Corollary 26 proves gamma > 0.0640 and q < 0.4278: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Corollary26.lean. Apply the balance in Remark 20 with grouping exponent 0.032: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem19.lean. The new numerical bound is a parameter refinement, not the paper’s stated rounded bound.

import Mathlib.Data.Rat.Init
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubquadratic3SUM.threeSum_above_2249_1125 (r : ℚ) (hr : (2249 / 1125 : ℚ) < r) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
