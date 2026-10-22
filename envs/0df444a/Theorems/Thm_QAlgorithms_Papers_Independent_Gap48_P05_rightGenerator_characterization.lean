-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P05_rightGenerator_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P05.rightGenerator_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:07:46.732357+00:00
-- url     : https://prove2.me/theorems/92c68438-0019-4973-b04b-50f5f4f3c292
-- title:
--   Infinitesimal generator of right multiplication
-- statement:
--   Let $\pi$ be a strongly continuous unitary representation of a Hausdorff locally convex Lie group $G$ with a smooth exponential function, and let $B(\mathcal H)_c$ denote the operator-norm continuous vectors for $\rho(g)A=A\pi(g)^{-1}$. Fix $x\in\mathfrak g$ and $A\in B(\mathcal H)_c$.
--
--   1. If $A\in\mathcal D(d\rho(x))$, the operator $A\overline{d\pi}(x)$ is bounded on its generator domain and
--   $$
--   (d\rho(x)A)v=-A\overline{d\pi}(x)v\qquad(v\in\mathcal D(\overline{d\pi}(x))).
--   $$
--   2. If $A\overline{d\pi}(x)^2$ is bounded on the domain of $\overline{d\pi}(x)^2$, then $A\in\mathcal D(d\rho(x))$.
--
--   These assertions retain the inverse in the action and the resulting negative sign in its generator.
-- source:
--   Smoothing operators and $C^*$-algebras for infinite dimensional Lie groups, arXiv:1505.02659v2, PDF p. 10, Lemma 2.3

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

/-- Lemma 2.3, PDF p. 10, both clauses. The first composition equality
is only on the generator domain and retains its essential negative sign. -/
theorem rightGenerator_characterization
    (L : ExponentialLieData E G) (pi : G →* (H ≃ₗᵢ[ℂ] H))
    (hAction : Continuous (fun p : G × H => pi p.1 p.2)) (x : E)
    (A : H →L[ℂ] H) (hCont : Continuous (fun g => rightInverseOperatorAction pi g A)) :
    (A ∈ GeneratorDomain L.exponential (rightInverseOperatorAction pi) x →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ v : H,
        v ∈ GeneratorDomain L.exponential (fun g v => pi g v) x →
        ‖A (infinitesimalGeneratorValue L.exponential (fun g v => pi g v) x v)‖ ≤ C * ‖v‖) ∧
      (∀ v : H, v ∈ GeneratorDomain L.exponential (fun g v => pi g v) x →
        (infinitesimalGeneratorValue L.exponential (rightInverseOperatorAction pi) x A) v =
          -A (infinitesimalGeneratorValue L.exponential (fun g v => pi g v) x v))) ∧
    ((∃ C : ℝ, 0 ≤ C ∧ ∀ v : H,
      WordDomain L.exponential (fun g v => pi g v) [x, x] v →
      ‖A (derivedWord L.exponential (fun g v => pi g v) [x, x] v)‖ ≤ C * ‖v‖) →
      A ∈ GeneratorDomain L.exponential (rightInverseOperatorAction pi) x) := by sorry

end HilbertOperators

end QAlgorithms.Papers.Independent.Gap48.P05
