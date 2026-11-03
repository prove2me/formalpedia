-- Prove2me | Theorems.Thm_RiskAverseConsistency_lemma_12
-- name    : RiskAverseConsistency.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:50.676524+00:00
-- url     : https://prove2.me/theorems/4f4fcfe6-05a0-4d68-9a82-8ec445612339
-- title:
--   Lemma 12 — the risk of the composed random objective is completely continuous
-- statement:
--   Let Assumption 10 hold and let $\mathcal R:L^p(\Omega,\mathcal F,P)\to\mathbb R$ be a convex risk measure, where $F(y)(\omega)=f(y,\xi(\omega))$ as in (9). Then the map
--
--   $$
--   Z_{\mathrm{ad}}\ni z\ \longmapsto\ \mathcal R[F(\mathbf Bz)]
--   $$
--
--   is completely continuous: $z_k\rightharpoonup z$ in $Z_{\mathrm{ad}}$ implies $\mathcal R[F(\mathbf Bz_k)]\to\mathcal R[F(\mathbf Bz)]$.
--
--   It gives existence of solutions of (8) by the direct method (Corollary 14 (a)).
--
--   Differences from the source:
--   - generalization: Ξ a complete separable metric space with its Borel σ-algebra 𝒜, (Ξ, 𝒜, ℙ) complete → Ξ an arbitrary measurable space, ξ measurable, ℙ := P.map ξ complete; reason: the topology of Ξ is never used; the paper's setting (with 𝒜 the ℙ-completed Borel σ-algebra, as its completeness assumption requires) is an instance
--   - encoding: f : Y₀ × Ξ → ℝ; F : Y₀ → Lᵖ(Ω, F, P) continuous → f : Y → Ξ → ℝ with every condition restricted to Y₀; continuity of F as ‖F(y_k) − F(y)‖_{Lᵖ} → 0 for (y_k) ⊂ Y₀, y_k → y ∈ Y₀; reason: Lean convention; sequential continuity is continuity on the metric space Y₀, and values off Y₀ are never used since B(Z_ad) ⊂ Y₀
--   - encoding: B : Z → Y linear and completely continuous → B : Z →ₗ[ℝ] Y with CompletelyContinuousOn univ B; reason: same instances; no boundedness is added
--   - encoding: ℛ applied to elements of Lᵖ(Ω, F, P) (F(Bz), Ĥ⁻¹(G(·))) → riskOf ℛ X = ℛ of the Lᵖ class of X when X ∈ Lᵖ, junk 0 otherwise; reason: every argument used is in Lᵖ (proved in the verification file), so the junk branch never fires
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.9, Lemma 12 (setting of §3, p.8)

import Mathlib
import Definitions.Def_RiskAverseConsistency_Assumption10
import Definitions.Def_RiskAverseConsistency_IsConvexRiskMeasure
import Definitions.Def_RiskAverseConsistency_riskOf
import Definitions.Def_RiskAverseConsistency_CompletelyContinuousOn

open MeasureTheory

namespace RiskAverseConsistency

/-- **Lemma 12.** If Assumption 10 holds and `ℛ : Lᵖ(Ω, F, P) → ℝ` is a convex risk measure, then
`Z_ad ∋ z ↦ ℛ[F(Bz)]` is completely continuous, where `F(y)(ω) = f(y, ξ(ω))`.

Milz, Surowiec, arXiv:2207.14756v2, Lemma 12, p.9.

Formalization Note (setting of §3, p.8, and §2, p.3): `Ξ` is an arbitrary measurable space and
`ℙ := P ∘ ξ⁻¹` is assumed complete (the paper: `Ξ` a complete separable metric space with its Borel
σ-algebra, `(Ξ, 𝒜, ℙ)` complete; its topology is never used). `ℛ` is applied to functions
`Ω → ℝ` through `riskOf`. -/
theorem lemma_12 {Ω Ξ Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ENNReal} (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → Ξ) (hξ : Measurable ξ)
    (hℙ_complete : (P.map ξ).IsComplete) {Zad : Set Z} {Y₀ : Set Y} (B : Z →ₗ[ℝ] Y) (φ : Z → ℝ)
    (f : Y → Ξ → ℝ) (hA : Assumption10 p P ξ Zad Y₀ B φ f) (ℛ : Lp ℝ p P → ℝ)
    (hℛ_convex : IsConvexRiskMeasure ℛ) :
    CompletelyContinuousOn Zad (fun z => riskOf ℛ (fun ω => f (B z) (ξ ω))) := by sorry

end RiskAverseConsistency
