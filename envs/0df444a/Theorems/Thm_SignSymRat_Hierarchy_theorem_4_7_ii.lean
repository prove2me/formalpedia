-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_theorem_4_7_ii
-- name    : SignSymRat.Hierarchy.theorem_4_7_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:33.52512+00:00
-- url     : https://prove2.me/theorems/7734b025-9356-44e1-8062-2de56c776c15
-- title:
--   Theorem 4.7(ii) — sparse hierarchy converges monotonically
-- statement:
--   For the sign-symmetry-adapted hierarchy (SDk), let $\rho_k^s$ be its order-$k$ value and let $\rho$ be the infimum of the original sum-of-ratios objective on $K$. Under Assumption 1.1, the Archimedean condition on $Q(g)$, and $N\ge2$,
--
--   $$\rho_k^s\nearrow\rho\qquad(k\to\infty).$$
--
--   Explicitly, the values are nondecreasing from $d_{\min}$ onward, each is at most $\rho$, and the sequence converges to $\rho$. This is the convergence guarantee for the paper's sparse block-diagonal SOS relaxations.
--
--   **Formalization Note** The paper's first ratio is Lean index `0`; other ratios have `i ≠ 0`. The added $N\ge2$ is necessary: with $N=1$, (4.2) can omit constraint supports from $A_1$, and the sparse claim can fail. The values are extended real, including $-\infty$ for infeasible (SDk) and $+\infty$ if $K$ is empty. The matrix pattern is governed by $\bar A$, not $A$.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 12, Theorem 4.7(ii)

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_SparseQM

namespace SignSymRat.Hierarchy

/-- Theorem 4.7(ii), p. 12: monotone convergence of the sparse hierarchy. -/
theorem theorem_4_7_ii {n m N : ℕ} (P : SRFO n m N) [NeZero N]
    (hN : 2 ≤ N) (hA : P.Assumption11) (hArch : IsArchimedean P.g) :
    (∀ k : ℕ, P.dmin ≤ k → P.rhoSK k ≤ P.rhoSK (k + 1)) ∧
    (∀ k : ℕ, P.dmin ≤ k → P.rhoSK k ≤ P.rho) ∧
    Filter.Tendsto (fun k : ℕ => P.rhoSK k) Filter.atTop (nhds P.rho) := by sorry

end SignSymRat.Hierarchy
