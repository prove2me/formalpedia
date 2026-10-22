-- Prove2me | Theorems.Thm_TraceClassRep_Characterization_eq_1
-- name    : TraceClassRep.Characterization.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:46.909996+00:00
-- url     : https://prove2.me/theorems/0b1f6706-8699-43bb-8ce6-11307e85eabf
-- title:
--   Equation (1) — Duflo-type distributional parametrix
-- statement:
--   For every $m\ge1$ and compact identity neighborhood $\Omega\subseteq G$, there are $k\ge1$, an open identity neighborhood $U\subseteq\Omega$, and $\beta,\gamma\in C^m_c(U)$ such that
--
--   $$(1-\Delta)^k\beta=\delta_1+\gamma.$$
--
--   The equality is distributional: it is tested against every smooth compactly supported function, using left Haar measure. This parametrix connects finite differentiability with the operator resolvent. It involves no representation or Hilbert space.
--
--   **Formalization Note** The test-function form uses the formally self-adjoint second-order right-invariant Laplacian. The group is a Hausdorff finite-dimensional normed-model Lie group with regular left Haar measure; the basis is arbitrary. The two test functions have compact support contained in $U$, and $k\ge1$.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, p. 5, Equation (1)

import Mathlib
import Definitions.Def_TraceClassRep_Characterization_Setting

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization
theorem eq_1
    {E G ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G] [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (b : Module.Basis ι ℝ E)
    (Ω : Set G) (hΩcompact : IsCompact Ω) (hΩone : Ω ∈ 𝓝 (1 : G))
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (k : ℕ) (U : Set G) (β γ : G → ℂ),
      1 ≤ k ∧ IsOpen U ∧ (1 : G) ∈ U ∧ U ⊆ Ω ∧
      IsCmCompact (E := E) m β ∧ IsCmCompact (E := E) m γ ∧
      tsupport β ⊆ U ∧ tsupport γ ⊆ U ∧
      ∀ φ : G → ℂ, IsSmoothCompact (E := E) φ →
        (∫ g, β g * oneSubLaplacianPow b k φ g ∂μ) =
          φ 1 + ∫ g, γ g * φ g ∂μ := by sorry

end TraceClassRep.Characterization
