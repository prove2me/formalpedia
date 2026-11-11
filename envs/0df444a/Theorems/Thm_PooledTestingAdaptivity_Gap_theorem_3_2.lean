-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_theorem_3_2
-- name    : PooledTestingAdaptivity.Gap.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:31.867319+00:00
-- url     : https://prove2.me/theorems/e07c2c87-8af0-46df-a7d0-97ebb83aca15
-- title:
--   Theorem 3.2 — Dynamic welfare is at most twice static welfare
-- statement:
--   Let $J$ be any general pooled-testing instance with $n\ge1$, arbitrary real utilities $u_i\ge0$, independent health probabilities $0<q_i\le1$ and an integer pool cap $G\ge1$. Let $B\ge0$ be an integer test budget. Suppose $\mathcal F$ is any nonempty health-independent family of ordered feasible allocations, each containing at most $B$ nonempty pools of size at most $G$, and is closed under shrinking pools and deleting tests in order. Then
--
--   $$\operatorname{OPT}_{\rm dyn}(B,J)\le2\operatorname{OPT}_{\rm stat}(B,J).$$
--
--   Both benchmarks are defined from their actual feasible policies and actual expected clearance utility. Dynamic feasibility holds on every health profile, including profiles with probability zero. Static pools may overlap or repeat, and additional feasibility constraints may depend on order. Zero budgets and zero welfare are included. The constant is exactly the paper's numeral $2$, uniform over all instance data and feasible families. This contains the standard-model bound of Theorem 3.1 and compares the full dynamic optimum with the overlapping static benchmark.
--
--   Differences from the source:
--   - encoding: people indexed by [n] and finite pool-labelled binary policies → people indexed by Fin n, health in Bool, and the published QTree with unit-valued stop leaves; reason: reindexing and tree constructors represent exactly the same health profiles, histories and policies
--   - encoding: optimal welfare, allowing health-independent randomized policies → real suprema of the actual feasible deterministic welfare sets; reason: bounded feasible lists give finite nonempty payoff sets; randomization averages deterministic values and cannot increase their maximum
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Theorem 3.2, Eq. (2), printed p. 6, PDF p. 7; proof §4.6, printed p. 18, PDF p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Policies

namespace PooledTestingAdaptivity.Gap

/-- Theorem 3.2, printed p.6 / PDF p.7; proved in §4.6, printed p.18.
No positivity of either optimum is assumed, and B may be zero. -/
theorem theorem_3_2 {n : ℕ} (J : Instance n) (B : ℕ)
    (F : FeasibleFamily J B) (hF : DownwardClosed F) :
    optDynamic F ≤ 2 * optStatic F := by sorry

end PooledTestingAdaptivity.Gap
