-- Prove2me | Theorems.Thm_ParetoEFX296_Approx_normal_form_reduction
-- name    : ParetoEFX296.Approx.normal_form_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:48.853456+00:00
-- url     : https://prove2.me/theorems/559eb49b-e77b-4a92-a396-9733b30b0ae6
-- title:
--   Proof of Theorem 2, Step 2 — swap improvement and square normal forms
-- statement:
--   For integer $K\ge6$, let $\alpha>2/3+1/K$ and suppose a complete allocation $A$ is both $\alpha$-EFX and Pareto optimal. If each large good is worth $2K+2$ to its owner, exchanging the owners of $x,y$ Pareto dominates $A$. Moreover, there is a table-preserving square symmetry sending $A$ to $A'$ that remains $\alpha$-EFX and Pareto optimal and satisfies one of
--   $$A'_1=\{x\},\ A'_2=\{y\},\ u_3(A')\ge u_4(A'),$$
--   $$A'_1=\{x\},\ A'_3=\{y\},\ e\in A'_2.$$
--   These are the normal forms used by the two cases. The reflections normalizing the last condition in each case appear at the start of those cases on page 10. This is the only milestone assuming Pareto optimality; it is a conditional reduction inside the contradiction argument.
--
--   Differences from the source:
--   - encoding: partitions of nine goods among agents 1,2,3,4 with integer K ≥ 6 → owner maps Good → Agent with named constructors, K : ℕ ≥ 6, and real table sums; reason: bijection with all complete integral allocations and all source integers K ≥ 6; real casts preserve every utility
--   - generalization: Definition 1 restricts α to (0,1] → the same distinct-agent EFX inequality is used for every real α above 2/3 + 1/K; reason: it agrees on the source range; for α > 1 positivity implies 1-EFX, and 1 > 2/3 + 1/K for K ≥ 6
--   - encoding: after rotation, and reflect at the start of each case → existence of table-preserving permutations and explicit transport of EFX and Pareto optimality; reason: makes the source relabelling and its normal forms precise without assuming their existence
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.10, Proof of Theorem 2, Step 2 opening and Cases 1–2 normalizations; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Instance

namespace ParetoEFX296.Approx

theorem normal_form_reduction (K : ℕ) (hK : 6 ≤ K) (α : ℝ) (hα : (2 : ℝ) / 3 + 1 / (K : ℝ) < α)
    (A : Allocation Agent Good) (hEFX : IsAlphaEFX (inst K) α A)
    (hPO : IsParetoOptimal (inst K) A) :
    ((inst K (A .x) .x = 2 * (K : ℝ) + 2 ∧
        inst K (A .y) .y = 2 * (K : ℝ) + 2) →
      ParetoDominates (inst K) (swapLarge A) A) ∧
    ∃ σ : SquareSymmetry K,
      IsAlphaEFX (inst K) α (relabel σ A) ∧
      IsParetoOptimal (inst K) (relabel σ A) ∧
      ((bundle (relabel σ A) .one = {Good.x} ∧
        bundle (relabel σ A) .two = {Good.y} ∧
        utility K (relabel σ A) .four ≤ utility K (relabel σ A) .three) ∨
       (bundle (relabel σ A) .one = {Good.x} ∧
        bundle (relabel σ A) .three = {Good.y} ∧
        (relabel σ A) .e = Agent.two)) := by sorry

end ParetoEFX296.Approx
