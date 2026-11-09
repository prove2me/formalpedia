-- Prove2me | Theorems.Thm_ParetoEFX296_Approx_adjacent_case_dominated
-- name    : ParetoEFX296.Approx.adjacent_case_dominated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:41.855908+00:00
-- url     : https://prove2.me/theorems/825e3eaf-7aca-4420-b467-226fcdeda14d
-- title:
--   Proof of Theorem 2, Step 2, Case 1 — bounds and domination by B₁
-- statement:
--   Let $K\ge6$ be integer, $\alpha>2/3+1/K$, and $A$ a complete $\alpha$-EFX allocation for the table. Suppose $A_1=\{x\}$, $A_2=\{y\}$ and $u(A)=(3K,3K,s,t)$ with $s\ge t$. Then
--   $$s\le2K+4,\quad t\le2K+2,\quad s+t\le4K+5,$$
--   $$u(B_1)=(3K,3K,2K+4,2K+2),\qquad B_1=(x,bce,yp,adq).$$
--   The named allocation $B_1$ Pareto dominates $A$, and $\sum_i u_i(B_1)\ge\sum_i u_i(A)+1$. This includes all three bounds, the constructed allocation's exact profile, and its strict Pareto improvement, covering the adjacent-lucky-agent case.
--
--   Differences from the source:
--   - encoding: partitions of nine goods among agents 1,2,3,4 with integer K ≥ 6 → owner maps Good → Agent with named constructors, K : ℕ ≥ 6, and real table sums; reason: bijection with all complete integral allocations and all source integers K ≥ 6; real casts preserve every utility
--   - generalization: Definition 1 restricts α to (0,1] → the same distinct-agent EFX inequality is used for every real α above 2/3 + 1/K; reason: it agrees on the source range; for α > 1 positivity implies 1-EFX, and 1 > 2/3 + 1/K for K ≥ 6
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.10, Proof of Theorem 2, Step 2, Case 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Instance

namespace ParetoEFX296.Approx

theorem adjacent_case_dominated (K : ℕ) (hK : 6 ≤ K) (α : ℝ) (hα : (2 : ℝ) / 3 + 1 / (K : ℝ) < α)
    (A : Allocation Agent Good) (hEFX : IsAlphaEFX (inst K) α A)
    (hx : bundle A .one = {Good.x}) (hy : bundle A .two = {Good.y})
    (s t : ℝ) (hu : utility K A = profile (3 * (K : ℝ)) (3 * (K : ℝ)) s t)
    (hst : t ≤ s) :
    s ≤ 2 * (K : ℝ) + 4 ∧ t ≤ 2 * (K : ℝ) + 2 ∧ s + t ≤ 4 * (K : ℝ) + 5 ∧
    utility K B₁ = profile (3 * (K : ℝ)) (3 * (K : ℝ))
      (2 * (K : ℝ) + 4) (2 * (K : ℝ) + 2) ∧
    ParetoDominates (inst K) B₁ A ∧
    (∑ i : Agent, utility K A i) + 1 ≤ ∑ i : Agent, utility K B₁ i := by sorry

end ParetoEFX296.Approx
