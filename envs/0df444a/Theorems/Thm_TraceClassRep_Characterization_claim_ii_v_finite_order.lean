-- Prove2me | Theorems.Thm_TraceClassRep_Characterization_claim_ii_v_finite_order
-- name    : TraceClassRep.Characterization.claim_ii_v_finite_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:49.229024+00:00
-- url     : https://prove2.me/theorems/7f78350d-7504-4b3c-bb2d-0c27b3292b41
-- title:
--   Theorem 1.3, proof of (ii) ⇒ (v) — a finite order on each compact neighborhood
-- statement:
--   Let $\Omega$ be a compact neighborhood of the identity in $G$. Assume $\pi:C^\infty_c(G)\to B_1(H)$ is continuous. Then some integer $m\ge1$ works for all $C^m$ functions supported in $\Omega$:
--
--   $$\exists m\ge1,\qquad \pi:C^m_\Omega(G)\longrightarrow B_1(H)\text{ extends continuously from }C^\infty_\Omega(G).$$
--
--   In particular, $\pi(C^m_\Omega(G))\subseteq B_1(H)$. The chosen $m$ and continuity bound may depend on $\Omega$.
--
--   **Formalization Note** The group is a Hausdorff finite-dimensional normed-model Lie group with regular left Haar measure, the Hilbert space need not be separable, and the unitary representation is strongly continuous. The arbitrary fixed Lie-algebra basis determines the Nelson Laplacian. Integrated operators are represented by their action on every vector. The genuine Schatten classes and extended Schatten norm are reused from TeschlQM; compact-support continuity is expressed by one seminorm bound per compact support set.
-- source:
--   van Dijk, Neeb, Salmasian, Zellner, On the characterization of trace class representations and Schwartz operators, arXiv:1512.02451v1, pp. 4–5, claim in the proof of Theorem 1.3, (ii) ⇒ (v)

import Mathlib
import Definitions.Def_TraceClassRep_Characterization_Setting

noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace TraceClassRep.Characterization
theorem claim_ii_v_finite_order
    {E G H ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype ι]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (b : Module.Basis ι ℝ E) (π : G →* (H ≃ₗᵢ[ℂ] H))
    (hstrong : ∀ v : H, Continuous (fun g : G => π g v))
    (hii : ConditionII b μ π) (Ω : Set G)
    (hΩcompact : IsCompact Ω) (hΩone : Ω ∈ 𝓝 (1 : G)) :
    ∃ m : ℕ, 1 ≤ m ∧
      (∀ f : G → ℂ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (m : WithTop ℕ∞) f →
        tsupport f ⊆ Ω →
        ∃ T : H →L[ℂ] H, IsIntegratedOp μ π f T ∧
          TeschlQM.TraceClass.IsTraceClass T) ∧
      ∃ C : ℝ≥0, ∀ (f : G → ℂ) (T : H →L[ℂ] H),
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (m : WithTop ℕ∞) f →
        tsupport f ⊆ Ω → IsIntegratedOp μ π f T →
        TeschlQM.TraceClass.schattenNorm 1 T ≤
          (C : ℝ≥0∞) * cmSeminorm b m f := by sorry

end TraceClassRep.Characterization
