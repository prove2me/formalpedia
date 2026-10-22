-- Prove2me | Theorems.Thm_TraceClassRep_Characterization_theorem_1_3_ii_v
-- name    : TraceClassRep.Characterization.theorem_1_3_ii_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:49.85428+00:00
-- url     : https://prove2.me/theorems/6790727a-afb1-4fd3-9d7d-9890c3c0a34b
-- title:
--   Theorem 1.3, (ii) ⇒ (v) — continuity implies a trace class resolvent power
-- statement:
--   Assume $\pi(C^\infty_c(G))\subseteq B_1(H)$ and $\pi:C^\infty_c(G)\to B_1(H)$ is continuous. With $D=\overline{d\pi(\Delta)}$, there is a positive integer $k$ such that
--
--   $$(1-D)^{-k}\in B_1(H).$$
--
--   This is the implication from the smooth test-function condition to the single-operator criterion.
--
--   **Formalization Note** The group is a Hausdorff finite-dimensional normed-model Lie group with regular left Haar measure, the Hilbert space need not be separable, and the unitary representation is strongly continuous. The arbitrary fixed Lie-algebra basis determines the Nelson Laplacian. Integrated operators are represented by their action on every vector. The genuine Schatten classes and extended Schatten norm are reused from TeschlQM; compact-support continuity is expressed by one seminorm bound per compact support set. The bounded operator $R$ is required to satisfy $R(w-d\pi(\Delta)w)=w$ for every smooth vector, which identifies it with $(1-D)^{-1}$.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, pp. 4–5, Theorem 1.3, (ii) ⇒ (v)

import Mathlib
import Definitions.Def_TraceClassRep_Characterization_Setting

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization
theorem theorem_1_3_ii_v
    {E G H ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (b : Module.Basis ι ℝ E) (π : G →* (H ≃ₗᵢ[ℂ] H))
    (hstrong : ∀ v : H, Continuous (fun g : G => π g v))
    (R : H →L[ℂ] H) (hR : IsLaplacianResolvent b π R)    (hii : ConditionII b μ π) : ConditionV R := by sorry

end TraceClassRep.Characterization
