-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_leftGenerator_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.leftGenerator_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:06:46.874323+00:00
-- url     : https://prove2.me/theorems/bc4baa75-bfca-4440-b213-a00a089e6bad
-- title:
--   Infinitesimal generator of left multiplication
-- statement:
--   Let $\pi$ be a strongly continuous unitary representation of a Hausdorff locally convex Lie group $G$ with a smooth exponential function. Let $B(\mathcal H)_c$ be the operator-norm continuous vectors for $\lambda(g)A=\pi(g)A$. Fix $x\in\mathfrak g$ and $A\in B(\mathcal H)_c$. The generators below are the full infinitesimal generators of the corresponding one-parameter groups.
--
--   1. If $A\in\mathcal D(d\lambda(x))$, then $A\mathcal H\subseteq\mathcal D(\overline{d\pi}(x))$ and
--   $$
--   (d\lambda(x)A)v=\overline{d\pi}(x)Av\qquad(v\in\mathcal H).
--   $$
--   2. If $\overline{d\pi}(x)^2A$ is defined on all of $\mathcal H$, then it is bounded and $A\in\mathcal D(d\lambda(x))$.
--
--   This identifies norm derivatives of the left operator orbit from Hilbert-space generator domains.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 9, Lemma 2.2

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

/-- Lemma 2.2, PDF pp. 9--10, both clauses: the all-H domain of the
square is a hypothesis and its boundedness is a conclusion. Derivatives
on B(H) use its operator norm, not the strong operator topology. -/
theorem leftGenerator_characterization
    (L : ExponentialLieData E G) (pi : G →* (H ≃ₗᵢ[ℂ] H))
    (hAction : Continuous (fun p : G × H => pi p.1 p.2)) (x : E)
    (A : H →L[ℂ] H) (hCont : Continuous (fun g => leftAction pi g A)) :
    (A ∈ GeneratorDomain L.exponential (leftAction pi) x →
      (∀ v : H, A v ∈ GeneratorDomain L.exponential (fun g v => pi g v) x) ∧
      (∀ v : H, (infinitesimalGeneratorValue L.exponential (leftAction pi) x A) v =
        infinitesimalGeneratorValue L.exponential (fun g v => pi g v) x (A v))) ∧
    ((∀ v : H, WordDomain L.exponential (fun g v => pi g v) [x, x] (A v)) →
      (∃ T : H →L[ℂ] H, ∀ v : H,
        T v = derivedWord L.exponential (fun g v => pi g v) [x, x] (A v)) ∧
      A ∈ GeneratorDomain L.exponential (leftAction pi) x) := by sorry

end HilbertOperators

end QAlgorithms.Papers.Independent.Gap48.P05
