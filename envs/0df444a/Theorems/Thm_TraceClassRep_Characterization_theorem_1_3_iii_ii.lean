-- Prove2me | Theorems.Thm_TraceClassRep_Characterization_theorem_1_3_iii_ii
-- name    : TraceClassRep.Characterization.theorem_1_3_iii_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:45.470325+00:00
-- url     : https://prove2.me/theorems/eab27fae-7091-4bf9-b9a5-225023c84db8
-- title:
--   Theorem 1.3, (iii) ⇒ (ii) — trace class images give continuity
-- statement:
--   Suppose $\pi(f)$ is trace class for every $f\in C^\infty_c(G)$. Then the integrated map is continuous into the trace-class ideal:
--
--   $$\pi:C^\infty_c(G)\longrightarrow B_1(H)\quad\text{is continuous}. $$
--
--   The conclusion retains the inclusion and gives, on each compact support set, one derivative order and one trace-norm bound valid for every supported smooth test function.
--
--   **Formalization Note** The group is a Hausdorff finite-dimensional normed-model Lie group with regular left Haar measure, the Hilbert space need not be separable, and the unitary representation is strongly continuous. The arbitrary fixed Lie-algebra basis determines the Nelson Laplacian. Integrated operators are represented by their action on every vector. The genuine Schatten classes and extended Schatten norm are reused from TeschlQM; compact-support continuity is expressed by one seminorm bound per compact support set.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, p. 4, Theorem 1.3, (iii) ⇒ (ii)

import Mathlib
import Definitions.Def_TraceClassRep_Characterization_Setting

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization
theorem theorem_1_3_iii_ii
    {E G H ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (b : Module.Basis ι ℝ E) (π : G →* (H ≃ₗᵢ[ℂ] H))
    (hstrong : ∀ v : H, Continuous (fun g : G => π g v))
    (hiii : ConditionIII (E := E) μ π) :
    ConditionII b μ π := by sorry

end TraceClassRep.Characterization
