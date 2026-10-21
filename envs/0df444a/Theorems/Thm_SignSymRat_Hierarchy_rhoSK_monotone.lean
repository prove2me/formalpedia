-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_rhoSK_monotone
-- name    : SignSymRat.Hierarchy.rhoSK_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:39.450977+00:00
-- url     : https://prove2.me/theorems/9edb6889-2ec9-4e35-bb1c-531ceab182a9
-- title:
--   Proof of Theorem 4.7(ii) — sparse bounds are monotone
-- statement:
--   For the order-$k$ sign-symmetric dual programs (SDk), let $\rho_k^s$ denote the extended-real optimal value and let $d_{\min}$ be the degree threshold from page 4. At every valid order,
--
--   $$k\ge d_{\min}\implies\rho_k^s\le\rho_{k+1}^s.$$
--
--   This is the monotonicity clause of the paper's convergence assertion.
--
--   **Formalization Note** The paper's ratio $1$ is Lean index `0`. The value $\rho_k^s$ is $-\infty$ when (SDk) is infeasible. The degree restriction on the auxiliary polynomials is the exact one from (SDk).
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 13, proof of Theorem 4.7(ii), first sentence

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_SparseQM

namespace SignSymRat.Hierarchy

/-- Monotonicity asserted in the proof of Theorem 4.7(ii), p. 13. -/
theorem rhoSK_monotone {n m N : ℕ} (P : SRFO n m N) [NeZero N] :
    ∀ k : ℕ, P.dmin ≤ k → P.rhoSK k ≤ P.rhoSK (k + 1) := by sorry

end SignSymRat.Hierarchy
