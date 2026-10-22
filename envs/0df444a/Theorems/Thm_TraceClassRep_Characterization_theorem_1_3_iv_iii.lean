-- Prove2me | Theorems.Thm_TraceClassRep_Characterization_theorem_1_3_iv_iii
-- name    : TraceClassRep.Characterization.theorem_1_3_iv_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:47.405812+00:00
-- url     : https://prove2.me/theorems/0f2c8bd6-fc7e-4fd6-a1ee-f1f10d5bd8ac
-- title:
--   Theorem 1.3, (iv) ⇒ (iii) — Hilbert–Schmidt images imply trace class
-- statement:
--   Suppose every $f\in C^\infty_c(G)$ has an integrated operator $\pi(f)$ in $B_2(H)$. Then
--
--   $$\pi(C^\infty_c(G))\subseteq B_1(H).$$
--
--   This is the Hilbert–Schmidt to trace-class implication in the five-way characterization. It uses the same integrated representation and Schatten ideals as the goal.
--
--   **Formalization Note** The group is a Hausdorff finite-dimensional normed-model Lie group with regular left Haar measure, the Hilbert space need not be separable, and the unitary representation is strongly continuous. The arbitrary fixed Lie-algebra basis determines the Nelson Laplacian. Integrated operators are represented by their action on every vector. The genuine Schatten classes and extended Schatten norm are reused from TeschlQM; compact-support continuity is expressed by one seminorm bound per compact support set.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, p. 4, Theorem 1.3, (iv) ⇒ (iii)

import Mathlib
import Definitions.Def_TraceClassRep_Characterization_Setting

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization
theorem theorem_1_3_iv_iii
    {E G H ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (b : Module.Basis ι ℝ E) (π : G →* (H ≃ₗᵢ[ℂ] H))
    (hstrong : ∀ v : H, Continuous (fun g : G => π g v))
    (hiv : ConditionIV (E := E) μ π) :
    ConditionIII (E := E) μ π := by sorry

end TraceClassRep.Characterization
