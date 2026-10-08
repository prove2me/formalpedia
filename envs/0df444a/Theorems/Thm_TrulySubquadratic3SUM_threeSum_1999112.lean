-- Prove2me | Theorems.Thm_TrulySubquadratic3SUM_threeSum_1999112
-- name    : TrulySubquadratic3SUM.threeSum_1999112
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T18:42:30.483801+00:00
-- url     : https://prove2.me/theorems/914126b2-461c-42b3-a5ef-9ab394fe8451
-- title:
--   3SUM in $O(n^{1.999112})$ word-RAM steps
-- statement:
--   For every fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural constant $b$, and a step bound $T$ that work for every input size $n$ and every word width $W\ge b(\operatorname{Nat.log2}(n)+1)$. On $n$ integers of absolute value at most $n^\kappa$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct indices have values summing to zero. Repeated values at distinct positions are allowed, and inputs with fewer than three positions are rejected.
--
--   The time bound is $T(n)=O(n^{1.999112})$: precisely, there is $K\in\mathbb N$ such that $T(n)^{125000}\le K n^{249889}$ for every $n\ge2$.
-- source:
--   Parameter refinement of Alman and Vassilevska Williams (2026), derived from Anthropic formal-math commit e1a4e6508154ea59f030480661590a9fe3018011. Corollary 26 proves gamma > 0.0640 and q < 0.4278: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Corollary26.lean. Apply the balance in Remark 20 with grouping exponent 0.032: https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem19.lean. The new numerical bound is a parameter refinement, not the paper’s stated rounded bound.

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem TrulySubquadratic3SUM.threeSum_1999112 :
    EndStatement.ThreeSum.SolvedInTime 1.999112 := by sorry
