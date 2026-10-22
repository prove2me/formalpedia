-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_identitySmoothing_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.identitySmoothing_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:09:21.806492+00:00
-- url     : https://prove2.me/theorems/0ac2ab52-19e8-41a6-b351-fde922c01268
-- title:
--   Identity smoothing and norm-smooth unitary representations
-- statement:
--   Let $\pi$ be a strongly continuous unitary representation of a Hausdorff locally convex Lie group $G$ with a smooth exponential function on a complex Hilbert space $\mathcal H$. Then
--
--   $$
--   \mathbf1\text{ is smoothing}\quad\Longleftrightarrow\quad\mathcal H^\infty=\mathcal H.
--   $$
--
--   If the Lie algebra $\mathfrak g$ is barreled, these conditions are equivalent to $\pi:G\to U(\mathcal H)$ being a morphism of Lie groups, where $U(\mathcal H)$ carries its operator-norm Banach–Lie group structure. This identifies precisely when every vector is smooth.
--
--   **Formalization Note** The already-given unitary group homomorphism is a norm Lie-group morphism exactly when its inclusion into $B(\mathcal H)$ is Bastiani smooth.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 13, Proposition 3.1

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

/-- Proposition 3.1, PDF p. 13: identity smoothing, all vectors smooth,
and, for a barreled Lie algebra, smoothness of the homomorphism into the
norm unitary Lie group. The last condition is equivalently its smoothness
into B(H), since U(H) is the norm Banach--Lie subgroup. -/
theorem identitySmoothing_characterization
    (L : ExponentialLieData E G) (pi : G →* (H ≃ₗᵢ[ℂ] H))
    (hAction : Continuous (fun p : G × H => pi p.1 p.2)) :
    (IsSmoothing (E := E) pi (ContinuousLinearMap.id ℂ H) ↔
      SmoothVectors (E := E) (fun g v => pi g v) = Set.univ) ∧
    (BarrelledSpace ℝ E →
      (IsSmoothing (E := E) pi (ContinuousLinearMap.id ℂ H) ↔
        BastianiSmoothMap (E := E) (unitaryOperator pi))) := by sorry

end HilbertOperators

end QAlgorithms.Papers.Independent.Gap48.P05
