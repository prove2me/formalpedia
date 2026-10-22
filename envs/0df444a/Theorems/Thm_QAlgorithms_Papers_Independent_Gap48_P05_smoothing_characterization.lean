-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_smoothing_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.smoothing_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:08:33.032034+00:00
-- url     : https://prove2.me/theorems/2ce24768-1705-46b6-acfb-12df31abeb6b
-- title:
--   Full characterization theorem for smoothing operators
-- statement:
--   Let $G$ be a Hausdorff locally convex Lie group with a smooth exponential function and let $\pi$ be a strongly continuous unitary representation on a complex Hilbert space $\mathcal H$ whose smooth-vector space $\mathcal H^\infty$ is dense. For $A\in B(\mathcal H)$, consider:
--
--   1. $g\mapsto\pi(g)A$ is smooth in operator norm.
--   2. $g\mapsto A^*\pi(g)$ is smooth in operator norm.
--   3. $A\mathcal H\subseteq\mathcal H^\infty$.
--   4. $A\mathcal H\subseteq\mathcal D^\infty$, the common domain of all finite generator products.
--   5. For each $D\in U(\mathfrak g_{\mathbb C})$, $A^*d\pi(D)$ is bounded on $\mathcal H^\infty$.
--
--   Then
--
--   $$
--   \text{(i)}\Longleftrightarrow\text{(ii)}\Longrightarrow\text{(iii)}\Longrightarrow\text{(iv)}\Longleftrightarrow\text{(v)}.
--   $$
--
--   If $\mathfrak g$ is metrizable, (iii) also implies (i) and (ii). If it is metrizable and Baire, all five conditions are equivalent. Moreover, (iii) implies that every $d\pi(D)A$ is bounded on all of $\mathcal H$. All smoothness uses the Bastiani calculus.
--
--   This is the full operator characterization, including the topology refinements and the final boundedness conclusion.
--
--   **Formalization Note** Elements of the derived enveloping-algebra image are evaluated as finite complex linear combinations of actual real generator words. Quantifying over all these representatives is equivalent to quantifying over $U(\mathfrak g_{\mathbb C})$.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 10, Theorem 2.1: full Characterization Theorem

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

/-- Theorem 2.1, PDF pp. 10--12: the complete implication diagram,
both topology refinements, and boundedness of every d pi(D) A.
Formal finite complex combinations of real derived words give exactly
the image of U(g_C), without requiring a separately supplied action.
Condition (ii) has A*, as printed. No Schwartz equivalence is asserted. -/
theorem smoothing_characterization
    (L : ExponentialLieData E G) (pi : G →* (H ≃ₗᵢ[ℂ] H))
    (hAction : Continuous (fun p : G × H => pi p.1 p.2))
    (hSmooth : Dense (SmoothVectors (E := E) (fun g v => pi g v)))
    (A : H →L[ℂ] H) :
    let c1 := BastianiSmoothMap (E := E) (fun g => leftAction pi g A)
    let c2 := BastianiSmoothMap (E := E)
      (fun g => A.adjoint.comp (unitaryOperator pi g))
    let c3 := IsSmoothing (E := E) pi A
    let c4 := ∀ v : H, A v ∈ DerivedInfinity L.exponential (fun g v => pi g v)
    let c5 := AdjointDerivedBounded L pi A
    (c1 ↔ c2) ∧ (c2 → c3) ∧ (c3 → c4) ∧ (c4 ↔ c5) ∧
    (TopologicalSpace.MetrizableSpace E → c3 → c1 ∧ c2) ∧
    (TopologicalSpace.MetrizableSpace E → BaireSpace E →
      (c1 ↔ c3) ∧ (c2 ↔ c3) ∧ (c3 ↔ c4) ∧ (c4 ↔ c5)) ∧
    (c3 → DerivedAfterBounded L pi A) := by sorry

end HilbertOperators

end QAlgorithms.Papers.Independent.Gap48.P05
