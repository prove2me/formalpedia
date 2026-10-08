-- Prove2me | Theorems.Thm_ServiceParts_UnitDecomp_critical_distance_policy_optimal
-- name    : ServiceParts.UnitDecomp.critical_distance_policy_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T21:57:43.910067+00:00
-- url     : https://prove2.me/theorems/b5ef24d1-bffc-47a1-a464-0c5d1b59ab15
-- title:
--   Section 2.2.1.2.2 — the critical distance policy $R_n$ is optimal for every subsystem
-- statement:
--   Consider a single-unit single-customer subsystem over a horizon of $N$ periods ($0<h<b$, $\alpha\in(0,1]$), with critical distance $y^*(n,s)$. The critical distance policy
--   $$R_n(s,y) = \mathit{Release} \iff y \le y^*(n,s)$$
--   is optimal: for every period $1\le n\le N$, every Markov state $s$ and every configuration $(z,y)$ of the subsystem with $y\ge 1$ whenever the unit is at the supplier ($z = m+1$),
--   $$C^{R}_n\big(s,(z,y)\big) = V_n\big(s,(z,y)\big).$$
--
--   Together with Theorem 4, this reduces an optimal policy for the whole system to one threshold per period and Markov state.
--
--   **Formalization Note** The policy is the book's, literally: release iff $y \le y^*(n,s)$, with $y^*$ possibly $\infty$ (then it always releases). Configurations with the unit at the supplier and the customer at distance $0$ are excluded because the book's rule would release there, which is suboptimal; they never occur in a subsystem started with its customer at distance at least 1.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 29, Section 2.2.1.2.2 (definition of y*(n, s_n) and the policy R_n; "Policy R_n is an optimal policy for every subsystem")

import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem

namespace ServiceParts.UnitDecomp

theorem critical_distance_policy_optimal {σ : Type} [Fintype σ] (M : Model σ) (N n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (s : σ) (z y : ℕ) (hzy : z = M.m + 1 → 1 ≤ y) :
    M.subCost N (M.criticalPolicy N) n s (z, y) = M.subOpt N n s (z, y) := by sorry

end ServiceParts.UnitDecomp
