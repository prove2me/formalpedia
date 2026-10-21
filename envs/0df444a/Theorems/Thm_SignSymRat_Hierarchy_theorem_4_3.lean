-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_theorem_4_3
-- name    : SignSymRat.Hierarchy.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:41.001583+00:00
-- url     : https://prove2.me/theorems/c35bb952-d8a3-4ce1-9a70-f34b341aebe8
-- title:
--   Theorem 4.3 — sign-symmetric dual has the original optimum
-- statement:
--   Let $\rho^s$ be the optimal value of (SD), whose auxiliary polynomials are supported in the symmetry closures $\bar A_i$. Under Assumption 1.1,
--
--   $$\rho^s=\rho.$$
--
--   This ensures that imposing the paper's sign-symmetry support restrictions does not change the untruncated dual optimum.
--
--   **Formalization Note** Paper index $1$ is Lean index `0`. No hypothesis $N\ge2$ is added: for $N=1$ (SD) has no auxiliary polynomials and its value is $\rho$ directly. Both values are extended real.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 10, Theorem 4.3

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_SignSym

namespace SignSymRat.Hierarchy

/-- Theorem 4.3, p. 10. -/
theorem theorem_4_3 {n m N : ℕ} (P : SRFO n m N) [NeZero N]
    (hA : P.Assumption11) : P.rhoS = P.rho := by sorry

end SignSymRat.Hierarchy
