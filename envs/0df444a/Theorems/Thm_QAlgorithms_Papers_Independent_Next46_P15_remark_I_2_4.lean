-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P15_remark_I_2_4
-- name    : QAlgorithms.Papers.Independent.Next46.P15.remark_I_2_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:16:40.15038+00:00
-- url     : https://prove2.me/theorems/2a2f6012-9465-422c-a7db-90d9a32b2c65
-- title:
--   Smoothness and derivatives of continuous multilinear maps
-- statement:
--   Let $k\ge0$, let $E_1,\ldots,E_k,F$ be Hausdorff real locally convex spaces, and let $m:E_1\times\cdots\times E_k\to F$ be continuous and multilinear. Then $m$ is continuously differentiable and smooth in the Michal–Bastiani sense, with
--   $$dm(x)h=\sum_{i=1}^{k}m(x_1,\ldots,x_{i-1},h_i,x_{i+1},\ldots,x_k),\qquad d^{k+1}m=0.$$
--   For $k=0$, the empty product is a singleton, so $m$ is constant and its first derivative vanishes.
--
--   This gives a basic class of smooth functions in locally convex calculus. Complex multilinear maps are included by restriction to the underlying real spaces.
-- source:
--   Towards a Lie theory for locally convex groups, arXiv:1501.06269v1, PDF p. 13, Remark I.2.4 (explicit unnumbered result)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P15

open Set Filter Topology

open scoped BigOperators

universe u v w z

/-- Remark I.2.4, PDF p.13: all continuous multilinear maps are smooth,
with the displayed first derivative and vanishing derivative of order k+1.
The heterogeneous product includes k=0, giving a constant map. -/
theorem remark_I_2_4
    (k : ℕ) (E : Fin k → Type u)
    [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)] [∀ i, T2Space (E i)]
    {F : Type v} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    (m : MultilinearMap ℝ E F) (hm : Continuous m) :
    IsMBCFiniteOn Set.univ (fun x => m x) 1 ∧
    IsMBSmoothOn Set.univ (fun x => m x) ∧
    (∀ x h : (i : Fin k) → E i,
      directionalDerivative (fun y => m y) x h =
        ∑ i : Fin k, m (Function.update x i (h i))) ∧
    (∀ (x : (i : Fin k) → E i) (h : Fin (k + 1) → ((i : Fin k) → E i)),
      iteratedDirectional (fun y => m y) (k + 1) x h = 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P15

end
