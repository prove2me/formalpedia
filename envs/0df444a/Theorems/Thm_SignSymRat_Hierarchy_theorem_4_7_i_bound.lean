-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_theorem_4_7_i_bound
-- name    : SignSymRat.Hierarchy.theorem_4_7_i_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:31.129991+00:00
-- url     : https://prove2.me/theorems/dea12298-5829-4454-95c1-9b50e0d616e3
-- title:
--   Theorem 4.7(i) — sparse bound versus dense bound
-- statement:
--   Let $\rho_k^s$ and $\rho_k$ be the values of the sign-symmetric and ordinary SOS dual relaxations (SDk) and (Dk) for the same sum-of-ratios problem. At every order $k\ge d_{\min}$,
--
--   $$\rho_k^s\le\rho_k.$$
--
--   This compares the sparse certificates with the unrestricted quadratic-module certificates and supports the upper-bound part of the convergence target.
--
--   **Formalization Note** Paper ratio $1$ is Lean index `0`. Both values are extended real. This item states the first claim of Theorem 4.7(i); its later equality claim under coinciding symmetry groups is outside the mission.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 12, Theorem 4.7(i), first claim

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_SparseQM

namespace SignSymRat.Hierarchy

/-- The first inequality of Theorem 4.7(i), p. 12. -/
theorem theorem_4_7_i_bound {n m N : ℕ} (P : SRFO n m N) [NeZero N] :
    ∀ k : ℕ, P.dmin ≤ k → P.rhoSK k ≤ P.rhoK k := by sorry

end SignSymRat.Hierarchy
