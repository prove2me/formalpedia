-- Prove2me | Theorems.Thm_TrulySubquadratic3SUM_threeSum_1999074
-- name    : TrulySubquadratic3SUM.threeSum_1999074
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T19:05:01.638026+00:00
-- url     : https://prove2.me/theorems/b6704d8b-ac74-45ed-8c21-3fbf0bb1f7a2
-- title:
--   3SUM in $O(n^{1.999074})$ word-RAM steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural constant $b$, and a step bound $T$ that work for every input size $n$ and every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. On $n$ integers of absolute value at most $n^\kappa$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct indices have values summing to zero. Repeated values at distinct positions are allowed, and inputs with fewer than three positions are rejected. The bound is $T(n)=O(n^{1.999074})$: precisely, there is $K\in\mathbb N$ such that $T(n)^{500000}\le K n^{999537}$ for every $n\ge2$.
-- source:
--   Open parameter-refinement target inspired by Alman and Vassilevska Williams (2026), using the existing Anthropic formal-math source at commit e1a4e6508154ea59f030480661590a9fe3018011. This target is proposed here, not asserted as a proved result of the paper. Generic inner construction: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/RunningTimes/Sec4/Corollary31_32.lean. Parameter estimates: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Table2.lean.

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubquadratic3SUM.threeSum_1999074 :
    EndStatement.ThreeSum.SolvedInTime 1.999074 := by sorry
