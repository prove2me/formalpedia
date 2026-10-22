-- Prove2me | Theorems.Thm_TraceClassRep_Characterization_theorem_1_3
-- name    : TraceClassRep.Characterization.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:49.775282+00:00
-- url     : https://prove2.me/theorems/2323dcc6-b4de-44c1-81c5-6906292c4ff6
-- title:
--   Theorem 1.3 — five characterizations of trace class representations
-- statement:
--   Let $G$ be a finite-dimensional Lie group and $\pi$ a strongly continuous unitary representation on a complex Hilbert space $H$. Fix a Lie-algebra basis and write $D=\overline{d\pi(\Delta)}$ for the closed Nelson Laplacian. The following conditions are equivalent:
--
--   $$
--   \begin{aligned}
--   \text{(i)}&\quad \exists m\ge1:\ \pi(C^m_c(G))\subseteq B_1(H)\text{ continuously};\
--   \text{(ii)}&\quad \pi(C^\infty_c(G))\subseteq B_1(H)\text{ continuously};\
--   \text{(iii)}&\quad \pi(C^\infty_c(G))\subseteq B_1(H);\
--   \text{(iv)}&\quad \pi(C^\infty_c(G))\subseteq B_2(H);\
--   \text{(v)}&\quad \exists k\ge1:\ (1-D)^{-k}\in B_1(H).
--   \end{aligned}
--   $$
--
--   This is the paper's main trace-class characterization, including both continuity clauses and all five conditions.
--
--   **Formalization Note** The group is a Hausdorff finite-dimensional normed-model Lie group with regular left Haar measure, the Hilbert space need not be separable, and the unitary representation is strongly continuous. The arbitrary fixed Lie-algebra basis determines the Nelson Laplacian. Integrated operators are represented by their action on every vector. The genuine Schatten classes and extended Schatten norm are reused from TeschlQM; compact-support continuity is expressed by one seminorm bound per compact support set. The bounded resolvent $R$ is characterized by $R(w-d\pi(\Delta)w)=w$ on every smooth vector and thus represents $(1-D)^{-1}$; its existence is ensured by the cited non-positive self-adjointness theorem.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, pp. 3–4, Theorem 1.3

import Mathlib
import Definitions.Def_TraceClassRep_Characterization_Setting

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization
theorem theorem_1_3
    {E G H ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (b : Module.Basis ι ℝ E) (π : G →* (H ≃ₗᵢ[ℂ] H))
    (hstrong : ∀ v : H, Continuous (fun g : G => π g v))
    (R : H →L[ℂ] H) (hR : IsLaplacianResolvent b π R)    : List.TFAE [ConditionI b μ π, ConditionII b μ π,
        ConditionIII (E := E) μ π, ConditionIV (E := E) μ π, ConditionV R] := by sorry

end TraceClassRep.Characterization
