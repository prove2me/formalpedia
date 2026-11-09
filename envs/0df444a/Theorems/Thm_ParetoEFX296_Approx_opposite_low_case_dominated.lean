-- Prove2me | Theorems.Thm_ParetoEFX296_Approx_opposite_low_case_dominated
-- name    : ParetoEFX296.Approx.opposite_low_case_dominated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:54.182808+00:00
-- url     : https://prove2.me/theorems/505fe053-9850-4a3a-a6ff-dffc2dae4fea
-- title:
--   Proof of Theorem 2, Step 2, Case 2 — bounds and domination by B₂ when s ≤ 3K
-- statement:
--   Let $K\ge6$ be integer, $\alpha>2/3+1/K$, and $A$ a complete $\alpha$-EFX allocation. Suppose $A_1=\{x\}$, $A_3=\{y\}$, $e\in A_2$ and $u(A)=(3K,s,2K+2,t)$. Then
--   $$s+t\le5K+3,\qquad t\le2K+4.$$
--   If $s\le3K$, the allocation $B_2=(abe,y,cdp,xq)$ satisfies
--   $$u(B_2)=(3K,3K,2K+2,2K+4),$$
--   Pareto dominates $A$, and has total utility at least one larger. There is no assumption $s\ge t$. The unconditional bounds and conditional domination constitute the lower-utility branch of Case 2.
--
--   Differences from the source:
--   - encoding: partitions of nine goods among agents 1,2,3,4 with integer K ≥ 6 → owner maps Good → Agent with named constructors, K : ℕ ≥ 6, and real table sums; reason: bijection with all complete integral allocations and all source integers K ≥ 6; real casts preserve every utility
--   - generalization: Definition 1 restricts α to (0,1] → the same distinct-agent EFX inequality is used for every real α above 2/3 + 1/K; reason: it agrees on the source range; for α > 1 positivity implies 1-EFX, and 1 > 2/3 + 1/K for K ≥ 6
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.10, Proof of Theorem 2, Step 2, Case 2, s ≤ 3K; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Instance

namespace ParetoEFX296.Approx

theorem opposite_low_case_dominated (K : ℕ) (hK : 6 ≤ K) (α : ℝ) (hα : (2 : ℝ) / 3 + 1 / (K : ℝ) < α)
    (A : Allocation Agent Good) (hEFX : IsAlphaEFX (inst K) α A)
    (hx : bundle A .one = {Good.x}) (hy : bundle A .three = {Good.y})
    (he : A .e = Agent.two) (s t : ℝ)
    (hu : utility K A = profile (3 * (K : ℝ)) s (2 * (K : ℝ) + 2) t) :
    s + t ≤ 5 * (K : ℝ) + 3 ∧ t ≤ 2 * (K : ℝ) + 4 ∧
    (s ≤ 3 * (K : ℝ) →
      utility K B₂ = profile (3 * (K : ℝ)) (3 * (K : ℝ))
        (2 * (K : ℝ) + 2) (2 * (K : ℝ) + 4) ∧
      ParetoDominates (inst K) B₂ A ∧
      (∑ i : Agent, utility K A i) + 1 ≤ ∑ i : Agent, utility K B₂ i) := by sorry

end ParetoEFX296.Approx
