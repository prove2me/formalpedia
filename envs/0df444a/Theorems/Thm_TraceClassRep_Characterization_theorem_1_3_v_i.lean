-- Prove2me | Theorems.Thm_TraceClassRep_Characterization_theorem_1_3_v_i
-- name    : TraceClassRep.Characterization.theorem_1_3_v_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:58.481341+00:00
-- url     : https://prove2.me/theorems/4ad5308b-88cc-41f3-86b3-7cf83a1437d0
-- title:
--   Theorem 1.3, (v) ⇒ (i) — finite differentiability with m = 2k
-- statement:
--   If $R=(1-D)^{-1}$ and $R^k$ is trace class for some $k\ge1$, then the finite differentiability order can be taken to be $m=2k$:
--
--   $$\pi(C^{2k}_c(G))\subseteq B_1(H),\qquad \pi:C^{2k}_c(G)\to B_1(H)\text{ is continuous}. $$
--
--   The continuity is a trace-norm bound, uniform over functions with support in each fixed compact set. This is the quantitative final implication of Theorem 1.3.
--
--   **Formalization Note** The group is a Hausdorff finite-dimensional normed-model Lie group with regular left Haar measure, the Hilbert space need not be separable, and the unitary representation is strongly continuous. The arbitrary fixed Lie-algebra basis determines the Nelson Laplacian. Integrated operators are represented by their action on every vector. The genuine Schatten classes and extended Schatten norm are reused from TeschlQM; compact-support continuity is expressed by one seminorm bound per compact support set. The resolvent is characterized on smooth vectors and is not an arbitrary trace-class operator.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, p. 5, Theorem 1.3, (v) ⇒ (i)

import Mathlib
import Definitions.Def_TraceClassRep_Characterization_Setting

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization
theorem theorem_1_3_v_i
    {E G H ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (b : Module.Basis ι ℝ E) (π : G →* (H ≃ₗᵢ[ℂ] H))
    (hstrong : ∀ v : H, Continuous (fun g : G => π g v))
    (R : H →L[ℂ] H) (hR : IsLaplacianResolvent b π R)    (k : ℕ) (hk : 1 ≤ k)
    (htrace : TeschlQM.TraceClass.IsTraceClass (R ^ k)) :
    (∀ f : G → ℂ, IsCmCompact (E := E) (2 * k) f →
      ∃ T : H →L[ℂ] H, IsIntegratedOp μ π f T ∧ TeschlQM.TraceClass.IsTraceClass T) ∧
    (∀ K : Set G, IsCompact K → ∃ C : ℝ≥0,
      ∀ (f : G → ℂ) (T : H →L[ℂ] H),
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ((2 * k : ℕ) : WithTop ℕ∞) f →
        tsupport f ⊆ K → IsIntegratedOp μ π f T →
        TeschlQM.TraceClass.schattenNorm 1 T ≤ (C : ℝ≥0∞) * cmSeminorm b (2 * k) f) := by sorry

end TraceClassRep.Characterization
