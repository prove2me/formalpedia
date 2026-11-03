-- Prove2me | Theorems.Thm_RiskAverseConsistency_lemma_13
-- name    : RiskAverseConsistency.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:44.306144+00:00
-- url     : https://prove2.me/theorems/8028acd0-c394-43e9-a164-acf1e4bc0b66
-- title:
--   Lemma 13 — the empirical risk is a Carathéodory function of $(y,\omega')$
-- statement:
--   Let Assumption 10 hold, let $(\Omega,\mathcal F,P)$ be nonatomic and complete, and let $\mathcal R:L^p(\Omega,\mathcal F,P)\to\mathbb R$ be a convex, law invariant risk measure. Let $\xi^1,\xi^2,\dots$ be i.i.d. copies of $\xi$ on a complete probability space $(\Omega',\mathcal F',P')$, let $\hat H_{y,N}(\cdot;\omega')$ be the empirical distribution function of $f(y,\xi^1(\omega')),\dots,f(y,\xi^N(\omega'))$, and let $G:\Omega\to[0,1]$ be uniformly distributed. Then for each $N$,
--
--   $$
--   Y_0\times\Omega'\ni(y,\omega')\ \longmapsto\ \mathcal R\bigl[\hat H^{-1}_{y,N}(G(\cdot);\omega')\bigr]
--   $$
--
--   is a Carathéodory function: measurable in $\omega'$ for each $y\in Y_0$ and continuous on $Y_0$ for each $\omega'$.
--
--   It yields existence and measurability of empirical solutions (Corollary 14).
--
--   Differences from the source:
--   - generalization: Ξ a complete separable metric space with its Borel σ-algebra 𝒜, (Ξ, 𝒜, ℙ) complete → Ξ an arbitrary measurable space, ξ measurable, ℙ := P.map ξ complete; reason: the topology of Ξ is never used; the paper's setting (with 𝒜 the ℙ-completed Borel σ-algebra, as its completeness assumption requires) is an instance
--   - encoding: f : Y₀ × Ξ → ℝ; F : Y₀ → Lᵖ(Ω, F, P) continuous → f : Y → Ξ → ℝ with every condition restricted to Y₀; continuity of F as ‖F(y_k) − F(y)‖_{Lᵖ} → 0 for (y_k) ⊂ Y₀, y_k → y ∈ Y₀; reason: Lean convention; sequential continuity is continuity on the metric space Y₀, and values off Y₀ are never used since B(Z_ad) ⊂ Y₀
--   - encoding: B : Z → Y linear and completely continuous → B : Z →ₗ[ℝ] Y with CompletelyContinuousOn univ B; reason: same instances; no boundedness is added
--   - encoding: ℛ applied to elements of Lᵖ(Ω, F, P) (F(Bz), Ĥ⁻¹(G(·))) → riskOf ℛ X = ℛ of the Lᵖ class of X when X ∈ Lᵖ, junk 0 otherwise; reason: every argument used is in Lᵖ (proved in the verification file), so the junk branch never fires
--   - encoding: a fixed G : Ω → [0, 1] with uniform distribution ν (exists since P is nonatomic) → every measurable G : Ω → ℝ with P.map G = Lebesgue measure on [0, 1]; reason: such G takes values in [0, 1] almost surely, and the paper's statements do not depend on which G is chosen
--   - generalization: samples ξ¹, …, ξᴺ for N ∈ ℕ = {1, 2, …} → samples ξs 0, …, ξs (N−1), and the claim is made for every N ∈ ℕ including N = 0; reason: at N = 0 the empirical distribution function is 0 and the empirical risk is the constant ℛ(0); the claim also holds there, and for N ≥ 1 it is the paper's
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.9, Lemma 13 (setting of §3, p.8)

import Mathlib
import Definitions.Def_RiskAverseConsistency_Assumption10
import Definitions.Def_RiskAverseConsistency_IsConvexRiskMeasure
import Definitions.Def_RiskAverseConsistency_IsLawInvariant
import Definitions.Def_RiskAverseConsistency_IsNonatomic
import Definitions.Def_RiskAverseConsistency_empiricalRisk
import Definitions.Def_RiskAverseConsistency_IsCaratheodoryOn

open MeasureTheory

namespace RiskAverseConsistency

/-- **Lemma 13.** Let Assumption 10 hold, `(Ω, F, P)` be nonatomic and complete, and
`ℛ : Lᵖ(Ω, F, P) → ℝ` a convex, law invariant risk measure. Then, for each sample size `N`,
`Y₀ × Ω′ ∋ (y, ω′) ↦ ℛ[Ĥ⁻¹_{y,N}(G(·); ω′)]` is a Carathéodory function, where `Ĥ_{y,N}(·; ω′)` is
the empirical distribution function of `f(y, ξ¹(ω′)), …, f(y, ξᴺ(ω′))`.

Milz, Surowiec, arXiv:2207.14756v2, Lemma 13, p.9 (with the setting of p.8).

Formalization Note (setting of §3, p.8, and §2, p.3): `Ξ` is an arbitrary measurable space and
`ℙ := P ∘ ξ⁻¹` is assumed complete (the paper: `Ξ` a complete separable metric space with its Borel
σ-algebra, `(Ξ, 𝒜, ℙ)` complete; its topology is never used). `ℛ` is applied to functions
`Ω → ℝ` through `riskOf`. The samples `ξ¹, ξ², …` are `ξs 0, ξs 1, …`; the
uniform `G : Ω → [0,1]` is any measurable `G : Ω → ℝ` whose law is Lebesgue measure on `[0,1]`, and
the statement holds for each such `G` (by law invariance the choice does not matter). Nonatomic is
the classical notion `IsNonatomic`. -/
theorem lemma_13 {Ω Ξ Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
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
    (hG_law : P.map G = volume.restrict (Set.Icc (0 : ℝ) 1)) (N : ℕ) :
    IsCaratheodoryOn Y₀ (fun y ω' => empiricalRisk ℛ G (fun i => f y (ξs i ω')) N) := by sorry

end RiskAverseConsistency
