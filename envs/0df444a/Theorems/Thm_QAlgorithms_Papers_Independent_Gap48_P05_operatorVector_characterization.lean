-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_operatorVector_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.operatorVector_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:05:28.055593+00:00
-- url     : https://prove2.me/theorems/fa3df6d9-fca1-446b-bbde-072e29380cdb
-- title:
--   Differentiable vectors for left and two-sided operator actions
-- statement:
--   Let $\rho$ be a strongly continuous unitary representation of a Hausdorff locally convex Lie group $G$ with a smooth exponential function on a complex Hilbert space $\mathcal H$. Suppose that the $C^1$ vectors of $\rho$ are dense. Consider either the action $\lambda(g)A=\rho(g)A$ or the action $\alpha(g,h)A=\rho(g)A\rho(h)^{-1}$, in each case on its subspace $V$ of operator-norm continuous vectors in $B(\mathcal H)$. For every positive integer $k$ and $A\in V$,
--
--   $$
--   A\in V^k\quad\Longleftrightarrow\quad A\in\mathcal D^k
--   \text{ and all }\omega_A^n\text{ are continuous for }1\le n\le k.
--   $$
--
--   The domains and derived maps belong to the chosen action; for $\alpha$ their directions lie in $\mathfrak g\times\mathfrak g$. This supplies the operator-space differentiability criterion used in the smoothing characterization.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 7, Corollary 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P05

namespace QAlgorithms.Papers.Independent.Gap48.P05

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P05.productCharts

section HilbertOperators

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable [hETopAdd : IsTopologicalAddGroup E] [hESmul : ContinuousSMul ℝ E]

variable [hELocConv : LocallyConvexSpace ℝ E] [hET2 : T2Space E]

variable {G : Type v} [Group G] [TopologicalSpace G] [hGT2 : T2Space G]

variable [ChartedSpace E G]

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [hHComplete : CompleteSpace H]

include hETopAdd hESmul hELocConv hET2 hGT2 hHComplete

/-- Corollary 1.1, PDF p. 7, both representations. SOURCE CORRECTION:
the printed v in H is A in the indicated continuous-vector subspace of
B(H). The criterion is written in the ambient normed operator space;
its closed invariant continuous-vector subspace has the induced topology. -/
theorem operatorVector_characterization
    (L : ExponentialLieData E G) (pi : G →* (H ≃ₗᵢ[ℂ] H))
    (hAction : Continuous (fun p : G × H => pi p.1 p.2))
    (hDenseC1 : Dense {v : H | BastianiCkMap (E := E) 1 (fun g => pi g v)}) :
    (∀ k : ℕ, 0 < k → ∀ A : H →L[ℂ] H,
      Continuous (fun g => leftAction pi g A) →
      VectorCriterion L (leftAction pi) k A) ∧
    (∀ k : ℕ, 0 < k → ∀ A : H →L[ℂ] H,
      Continuous (fun p => alphaAction pi p A) →
      (BastianiCkMap (E := E × E) k (fun p => alphaAction pi p A) ↔
        A ∈ DerivedDomain
          (fun x : E × E => (L.exponential x.1, L.exponential x.2))
          (alphaAction pi) k ∧
        ∀ n, 0 < n → n ≤ k → Continuous (derivedTupleValue
          (fun x : E × E => (L.exponential x.1, L.exponential x.2))
          (alphaAction pi) n A))) := by sorry

end HilbertOperators

end QAlgorithms.Papers.Independent.Gap48.P05
