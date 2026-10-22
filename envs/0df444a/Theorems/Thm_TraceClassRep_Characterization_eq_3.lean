-- Prove2me | Theorems.Thm_TraceClassRep_Characterization_eq_3
-- name    : TraceClassRep.Characterization.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:49.697402+00:00
-- url     : https://prove2.me/theorems/abddaa8b-123c-4d5c-abb7-55dca1ec474c
-- title:
--   Equation (3), extended — integrated operator factorization
-- statement:
--   Let $R=(1-D)^{-1}$ and $k\ge1$. For every $f\in C^{2k}_c(G)$, the integrated operator identity is
--
--   $$\pi(f)=R^k\pi((1-\Delta)^k f).$$
--
--   This is Equation (3) and its finite-differentiability extension from the following paragraph, expressed as equality after application to every vector. The identity connects the function-side differential operator to the bounded resolvent.
--
--   **Formalization Note** The group is a Hausdorff finite-dimensional normed-model Lie group with regular left Haar measure, the Hilbert space need not be separable, and the unitary representation is strongly continuous. The arbitrary fixed Lie-algebra basis determines the Nelson Laplacian. Integrated operators are represented by their action on every vector. The genuine Schatten classes and extended Schatten norm are reused from TeschlQM; compact-support continuity is expressed by one seminorm bound per compact support set. The equality is stated for every positive $k$; the paper first displays it for the $k$ of condition (v), then extends it to $C^{2k}_c$.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, p. 5, Equation (3) and following paragraph

import Mathlib
import Definitions.Def_TraceClassRep_Characterization_Setting

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization
theorem eq_3
    {E G H ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (b : Module.Basis ι ℝ E) (π : G →* (H ≃ₗᵢ[ℂ] H))
    (hstrong : ∀ v : H, Continuous (fun g : G => π g v))
    (R : H →L[ℂ] H) (hR : IsLaplacianResolvent b π R)    (k : ℕ) (hk : 1 ≤ k) (f : G → ℂ)
    (hf : IsCmCompact (E := E) (2 * k) f) (v : H) :
    QAlgorithms.Papers.Independent.Renew46.P09.integratedVector μ (fun g => π g) f v =
      (R ^ k) (QAlgorithms.Papers.Independent.Renew46.P09.integratedVector μ
        (fun g => π g) (oneSubLaplacianPow b k f) v) := by sorry

end TraceClassRep.Characterization
