-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_theorem_3_1
-- name    : SignSymRat.Hierarchy.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:49.920261+00:00
-- url     : https://prove2.me/theorems/75b48b95-aca2-4767-9793-c3ed73e72b50
-- title:
--   Theorem 3.1 — polynomial dual has the original optimum
-- statement:
--   Let $\rho$ be the infimum of the sum-of-ratios objective on $K$, and let $\operatorname{val}(D)$ be the supremum of $c$ over the polynomial dual program (D). Under Assumption 1.1,
--
--   $$\operatorname{val}(D)=\rho.$$
--
--   This identifies the dual benchmark that the sign-symmetric restriction must recover.
--
--   **Formalization Note** The paper's first ratio is Lean index `0`. The statement allows one ratio, as the paper does. Both values are extended real, so empty or unbounded feasible sets receive their proper extended values.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 6, Theorem 3.1

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_Setting

namespace SignSymRat.Hierarchy

/-- Theorem 3.1, p. 6. -/
theorem theorem_3_1 {n m N : ℕ} (P : SRFO n m N) [NeZero N]
    (hA : P.Assumption11) : P.valD = P.rho := by sorry

end SignSymRat.Hierarchy
