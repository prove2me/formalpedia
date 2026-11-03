-- Prove2me | Theorems.Thm_RiskAverseConsistency_corollary_14
-- name    : RiskAverseConsistency.corollary_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:07.01376+00:00
-- url     : https://prove2.me/theorems/7f5e2a50-ccb6-4dcc-a8e4-384f5b96566b
-- title:
--   Corollary 14 — existence, closedness and measurability of true and empirical solutions
-- statement:
--   Under the hypotheses of Lemma 13, let $m^*$ and $\mathscr S$ be the optimal value and solution set of (8), $\min_{z\in Z_{\mathrm{ad}}}\mathcal R[F(\mathbf Bz)]+\wp(z)$, and let $\hat m^*_N$ and $\hat{\mathscr S}^r_N$ be the optimal value and set of $r$-minimizers of the empirical approximation (10), $\min_{z\in Z_{\mathrm{ad}}}\mathcal R[\hat H_{\mathbf Bz,N}]+\wp(z)$. Then
--
--   1. (a) $\mathscr S$ is nonempty and closed;
--   2. (b) $\hat{\mathscr S}^r_N(\omega')$ is nonempty and closed for each $r\in[0,\infty)$, each $N$ and each $\omega'$;
--   3. (c) for each $r\in[0,\infty)$ and each $N$, $\omega'\mapsto\hat m^*_N(\omega')$ is measurable and $\omega'\mapsto\hat{\mathscr S}^r_N(\omega')$ is a measurable set-valued map.
--
--   These facts make the almost sure statements of Theorem 11 meaningful.
--
--   Differences from the source:
--   - generalization: Ξ a complete separable metric space with its Borel σ-algebra 𝒜, (Ξ, 𝒜, ℙ) complete → Ξ an arbitrary measurable space, ξ measurable, ℙ := P.map ξ complete; reason: the topology of Ξ is never used; the paper's setting (with 𝒜 the ℙ-completed Borel σ-algebra, as its completeness assumption requires) is an instance
--   - encoding: f : Y₀ × Ξ → ℝ; F : Y₀ → Lᵖ(Ω, F, P) continuous → f : Y → Ξ → ℝ with every condition restricted to Y₀; continuity of F as ‖F(y_k) − F(y)‖_{Lᵖ} → 0 for (y_k) ⊂ Y₀, y_k → y ∈ Y₀; reason: Lean convention; sequential continuity is continuity on the metric space Y₀, and values off Y₀ are never used since B(Z_ad) ⊂ Y₀
--   - encoding: B : Z → Y linear and completely continuous → B : Z →ₗ[ℝ] Y with CompletelyContinuousOn univ B; reason: same instances; no boundedness is added
--   - encoding: ℛ applied to elements of Lᵖ(Ω, F, P) (F(Bz), Ĥ⁻¹(G(·))) → riskOf ℛ X = ℛ of the Lᵖ class of X when X ∈ Lᵖ, junk 0 otherwise; reason: every argument used is in Lᵖ (proved in the verification file), so the junk branch never fires
--   - encoding: a fixed G : Ω → [0, 1] with uniform distribution ν (exists since P is nonatomic) → every measurable G : Ω → ℝ with P.map G = Lebesgue measure on [0, 1]; reason: such G takes values in [0, 1] almost surely, and the paper's statements do not depend on which G is chosen
--   - generalization: samples ξ¹, …, ξᴺ for N ∈ ℕ = {1, 2, …} → samples ξs 0, …, ξs (N−1), and the claim is made for every N ∈ ℕ including N = 0; reason: at N = 0 the empirical distribution function is 0 and the empirical risk is the constant ℛ(0); the claim also holds there, and for N ≥ 1 it is the paper's
--   - encoding: m̂*_N measurable (real-valued) → m̂*_N measurable as an EReal-valued map; reason: m̂*_N is finite by (b); the inclusion ℝ → EReal is a measurable embedding
--   - reading: Ŝ^r_N is measurable (no definition in the paper; reference [5]) → {ω′ : Ŝ^r_N(ω′) ∩ U ≠ ∅} ∈ F′ for every open U ⊂ Z; reason: the definition of measurable set-valued maps in the cited reference [5], Aubin–Frankowska Def. 8.1.1
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.10, Corollary 14; (8), (10), pp.8–9

import Mathlib
import Definitions.Def_RiskAverseConsistency_Assumption10
import Definitions.Def_RiskAverseConsistency_IsConvexRiskMeasure
import Definitions.Def_RiskAverseConsistency_IsLawInvariant
import Definitions.Def_RiskAverseConsistency_IsNonatomic
import Definitions.Def_RiskAverseConsistency_trueObjective
import Definitions.Def_RiskAverseConsistency_empiricalObjective
import Definitions.Def_RiskAverseConsistency_optimalValue
import Definitions.Def_RiskAverseConsistency_epsSolutionSet
import Definitions.Def_RiskAverseConsistency_solutionSet
import Definitions.Def_RiskAverseConsistency_IsMeasurableSetValued

open MeasureTheory

namespace RiskAverseConsistency

/-- **Corollary 14.** Under the hypotheses of Lemma 13, (a) the solution set `𝒮` of (8) is nonempty
and closed, (b) the set `Ŝ^r_N` of `r`-minimizers of (10) has nonempty, closed images for each
`r ∈ [0, ∞)`, and (c) the optimal value `m̂*_N` of (10) and `Ŝ^r_N` are measurable for each
`r ∈ [0, ∞)`.

Milz, Surowiec, arXiv:2207.14756v2, Corollary 14, p.10; (8), (10), pp.8–9.

Formalization Note (setting of §3, p.8, and §2, p.3): `Ξ` is an arbitrary measurable space and
`ℙ := P ∘ ξ⁻¹` is assumed complete (the paper: `Ξ` a complete separable metric space with its Borel
σ-algebra, `(Ξ, 𝒜, ℙ)` complete; its topology is never used). `ℛ` is applied to functions
`Ω → ℝ` through `riskOf`. The samples `ξ¹, ξ², …` are `ξs 0, ξs 1, …`; the
uniform `G : Ω → [0,1]` is any measurable `G : Ω → ℝ` whose law is Lebesgue measure on `[0,1]`, and
the statement holds for each such `G` (by law invariance the choice does not matter). Nonatomic is
the classical notion `IsNonatomic`. The objectives of (8) and (10) are
`trueObjective` and `empiricalObjective` (cast to `EReal`); `m̂*_N = optimalValue`,
`Ŝ^r_N = epsSolutionSet`, `𝒮 = solutionSet`, all over `Z_ad`. (b) and (c) are stated for every
sample size `N` and (b) for every `ω′`. Measurability of `m̂*_N` is as an `EReal`-valued map on
`(Ω′, F′)`; measurability of the set-valued map `Ŝ^r_N` is `IsMeasurableSetValued`. -/
theorem corollary_14 {Ω Ξ Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ENNReal} (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → Ξ) (hξ : Measurable ξ)
    (hℙ_complete : (P.map ξ).IsComplete) {Zad : Set Z} {Y₀ : Set Y} (B : Z →ₗ[ℝ] Y) (φ : Z → ℝ)
    (f : Y → Ξ → ℝ) (hA : Assumption10 p P ξ Zad Y₀ B φ f) (ℛ : Lp ℝ p P → ℝ)
    (hℛ_convex : IsConvexRiskMeasure ℛ)
    (hP_nonatomic : IsNonatomic P) (hP_complete : P.IsComplete)
    (hℛ_law : IsLawInvariant ℛ) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (hP'_complete : P'.IsComplete) (ξs : ℕ → Ω' → Ξ)
    (hξs_meas : ∀ i, Measurable (ξs i)) (hξs_indep : ProbabilityTheory.iIndepFun ξs P')
    (hξs_law : ∀ i, P'.map (ξs i) = P.map ξ) (G : Ω → ℝ) (hG_meas : Measurable G)
    (hG_law : P.map G = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    ((solutionSet Zad (trueObjective ℛ ξ f B φ)).Nonempty ∧
        IsClosed (solutionSet Zad (trueObjective ℛ ξ f B φ))) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ (N : ℕ) (ω' : Ω'),
        (epsSolutionSet Zad (empiricalObjective ℛ G ξs f B φ N ω') r).Nonempty ∧
          IsClosed (epsSolutionSet Zad (empiricalObjective ℛ G ξs f B φ N ω') r)) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ N : ℕ,
        Measurable (fun ω' => optimalValue Zad (empiricalObjective ℛ G ξs f B φ N ω')) ∧
          IsMeasurableSetValued
            (fun ω' => epsSolutionSet Zad (empiricalObjective ℛ G ξs f B φ N ω') r)) := by sorry

end RiskAverseConsistency
