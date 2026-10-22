-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_frechet_smoothing_iff_normSmoothOrbit
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.frechet_smoothing_iff_normSmoothOrbit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:02:50.675397+00:00
-- url     : https://prove2.me/theorems/791eb564-e139-46a3-ba98-d82582e524a8
-- title:
--   Smoothing operators for Frechet--Lie groups
-- statement:
--   Let $G$ be a real Hausdorff locally convex Fréchet–Lie group with a smooth exponential function, and let $\pi$ be a strongly continuous unitary representation on a complex Hilbert space $\mathcal H$. Assume that its space $\mathcal H^\infty$ of smooth vectors is dense. A bounded operator $A$ is smoothing when $A\mathcal H\subseteq\mathcal H^\infty$. Then
--
--   $$
--   A\mathcal H\subseteq\mathcal H^\infty
--   \quad\Longleftrightarrow\quad
--   [g\mapsto\pi(g)A]\in C^\infty(G,B(\mathcal H)).
--   $$
--
--   Smoothness on the right uses the operator norm and the Bastiani calculus. This characterizes the range condition by regularity of a bounded-operator orbit.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 1, Abstract, first main result: smoothing versus norm-smooth orbit (Fréchet specialization)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P05

namespace QAlgorithms.Papers.Independent.Gap48.P05

open Set Filter Topology

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P05.productCharts

/-- Abstract first main result (PDF p. 1), with the precise smooth
representation hypothesis from Theorem 2.1 (PDF p. 10), specialized to a
Frechet real locally convex model. Frechet completeness is the compatible
additive uniformity, not a norm on the model. -/
theorem frechet_smoothing_iff_normSmoothOrbit
    {E : Type u} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [IsUniformAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] [TopologicalSpace.MetrizableSpace E] [CompleteSpace E]
    {G : Type v} [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G]
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : ExponentialLieData E G) (pi : G →* (H ≃ₗᵢ[ℂ] H))
    (hAction : Continuous (fun p : G × H => pi p.1 p.2))
    (hSmooth : Dense (SmoothVectors (E := E) (fun g v => pi g v)))
    (A : H →L[ℂ] H) :
    IsSmoothing (E := E) pi A ↔
      BastianiSmoothMap (E := E) (fun g => leftAction pi g A) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P05
