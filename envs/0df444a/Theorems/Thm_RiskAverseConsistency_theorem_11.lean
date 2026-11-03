-- Prove2me | Theorems.Thm_RiskAverseConsistency_theorem_11
-- name    : RiskAverseConsistency.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:24:14.422884+00:00
-- url     : https://prove2.me/theorems/6c189cad-fb64-4e76-8551-f1706e3e7b5d
-- title:
--   Theorem 11 — almost sure consistency of empirical optimal values and approximate solution sets
-- statement:
--   Let Assumption 10 hold, let $(\Omega,\mathcal F,P)$ be nonatomic and complete, and let $\mathcal R:L^p(\Omega,\mathcal F,P)\to\mathbb R$ be a convex, law invariant risk measure. Consider the risk-averse problem
--
--   $$
--   \min_{z\in Z_{\mathrm{ad}}}\ \mathcal R[F(\mathbf Bz)]+\wp(z),\qquad F(y)(\omega)=f(y,\xi(\omega)),\tag{8}
--   $$
--
--   with optimal value $m^*$ and solution set $\mathscr S$, and its empirical approximation
--
--   $$
--   \min_{z\in Z_{\mathrm{ad}}}\ \mathcal R[\hat H_{\mathbf Bz,N}]+\wp(z),\tag{10}
--   $$
--
--   where $\hat H_{y,N}(\cdot;\omega')$ is the empirical distribution function of $f(y,\xi^1(\omega')),\dots,f(y,\xi^N(\omega'))$ for i.i.d. copies $\xi^1,\xi^2,\dots$ of $\xi$ on a complete probability space $(\Omega',\mathcal F',P')$, and $\mathcal R[\hat H_{y,N}]=\mathcal R[\hat H^{-1}_{y,N}(G(\cdot);\omega')]$ for a uniform $G:\Omega\to[0,1]$. Let $\hat m^*_N$ be the optimal value of (10) and $\hat{\mathscr S}^r_N$ its set of $r$-minimizers. If $(r_N)\subset[0,\infty)$ is a deterministic sequence with $r_N\to0$, then
--
--   $$
--   \hat m^*_N\to m^*\qquad\text{with }P'\text{-probability one as }N\to\infty .
--   $$
--
--   If furthermore $\wp$ is an R-function, then
--
--   $$
--   \mathbb D\bigl(\hat{\mathscr S}^{r_N}_N,\mathscr S\bigr)\to0\qquad\text{with }P'\text{-probability one as }N\to\infty .
--   $$
--
--   This is the main result of the paper: sample-based (plug-in) approximations of nonconvex risk-averse programs over infinite dimensional decision spaces are consistent, for every real-valued law invariant convex risk measure.
--
--   Differences from the source:
--   - generalization: Ξ a complete separable metric space with its Borel σ-algebra 𝒜, (Ξ, 𝒜, ℙ) complete → Ξ an arbitrary measurable space, ξ measurable, ℙ := P.map ξ complete; reason: the topology of Ξ is never used; the paper's setting (with 𝒜 the ℙ-completed Borel σ-algebra, as its completeness assumption requires) is an instance
--   - encoding: f : Y₀ × Ξ → ℝ; F : Y₀ → Lᵖ(Ω, F, P) continuous → f : Y → Ξ → ℝ with every condition restricted to Y₀; continuity of F as ‖F(y_k) − F(y)‖_{Lᵖ} → 0 for (y_k) ⊂ Y₀, y_k → y ∈ Y₀; reason: Lean convention; sequential continuity is continuity on the metric space Y₀, and values off Y₀ are never used since B(Z_ad) ⊂ Y₀
--   - encoding: B : Z → Y linear and completely continuous → B : Z →ₗ[ℝ] Y with CompletelyContinuousOn univ B; reason: same instances; no boundedness is added
--   - encoding: ℛ applied to elements of Lᵖ(Ω, F, P) (F(Bz), Ĥ⁻¹(G(·))) → riskOf ℛ X = ℛ of the Lᵖ class of X when X ∈ Lᵖ, junk 0 otherwise; reason: every argument used is in Lᵖ (proved in the verification file), so the junk branch never fires
--   - encoding: a fixed G : Ω → [0, 1] with uniform distribution ν (exists since P is nonatomic) → every measurable G : Ω → ℝ with P.map G = Lebesgue measure on [0, 1]; reason: such G takes values in [0, 1] almost surely, and the paper's statements do not depend on which G is chosen
--   - encoding: samples ξ¹, …, ξᴺ, N ∈ ℕ = {1, 2, …} → samples ξs 0, …, ξs (N−1); N ranges over ℕ including 0; reason: index shift; only N → ∞ enters the statement
--   - encoding: optimal values m*, m̂*_N as real numbers → optimal values as infima in EReal of the real objectives; reason: both are finite under the hypotheses (Corollary 14), so convergence in EReal is convergence in ℝ
--   - encoding: 𝔻(Γ, Ψ) = sup dist(x, Ψ) as a real number → the published CompositeSAA.excess, valued in [0, ∞] (ENNReal), converging to 0 there; reason: Lean convention; the deviation of nonempty sets inside a bounded set from a nonempty set is finite, and convergence to 0 is the same
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.9, Theorem 11; (8)–(10), pp.8–9; Assumption 10, p.9

import Mathlib
import Definitions.Def_RiskAverseConsistency_Assumption10
import Definitions.Def_RiskAverseConsistency_IsConvexRiskMeasure
import Definitions.Def_RiskAverseConsistency_IsLawInvariant
import Definitions.Def_RiskAverseConsistency_IsNonatomic
import Definitions.Def_RiskAverseConsistency_IsRFunction
import Definitions.Def_RiskAverseConsistency_trueObjective
import Definitions.Def_RiskAverseConsistency_empiricalObjective
import Definitions.Def_RiskAverseConsistency_optimalValue
import Definitions.Def_RiskAverseConsistency_epsSolutionSet
import Definitions.Def_RiskAverseConsistency_solutionSet
import Definitions.Def_CompositeSAA_excess

open MeasureTheory Filter Topology

namespace RiskAverseConsistency

/-- **Theorem 11** (consistency of the empirical approximation). Let Assumption 10 hold, let
`(Ω, F, P)` be nonatomic and complete, and let `ℛ : Lᵖ(Ω, F, P) → ℝ` be a convex, law invariant
risk measure. If `(r_N) ⊂ [0, ∞)` is a deterministic sequence with `r_N → 0`, then `m̂*_N → m*`
with `P′`-probability one. If furthermore `℘` is an R-function, then `𝔻(Ŝ^{r_N}_N, 𝒮) → 0` with
`P′`-probability one. Here `m* = inf_{z ∈ Z_ad} ℛ[F(Bz)] + ℘(z)` and `𝒮` are the optimal value and
solution set of (8), and `m̂*_N` and `Ŝ^r_N` the optimal value and set of `r`-minimizers of the
empirical approximation (10), `min_{z ∈ Z_ad} ℛ[Ĥ_{Bz,N}] + ℘(z)`.

Milz, Surowiec, arXiv:2207.14756v2, Theorem 11, p.9; (8)–(10), pp.8–9.

Formalization Note (setting of §3, p.8, and §2, p.3): `Ξ` is an arbitrary measurable space and
`ℙ := P ∘ ξ⁻¹` is assumed complete (the paper: `Ξ` a complete separable metric space with its Borel
σ-algebra, `(Ξ, 𝒜, ℙ)` complete; its topology is never used). `ℛ` is applied to functions
`Ω → ℝ` through `riskOf`. The samples `ξ¹, ξ², …` are `ξs 0, ξs 1, …`; the
uniform `G : Ω → [0,1]` is any measurable `G : Ω → ℝ` whose law is Lebesgue measure on `[0,1]`, and
the statement holds for each such `G` (by law invariance the choice does not matter). Nonatomic is
the classical notion `IsNonatomic`. The objectives of (8) and (10) are
`trueObjective` and `empiricalObjective` cast to `EReal`; `m*`, `m̂*_N` are `optimalValue` (in
`EReal`), `Ŝ^r_N = epsSolutionSet`, `𝒮 = solutionSet`, all over `Z_ad`; `𝔻` is the published `CompositeSAA.excess` in
`[0, ∞]`. "With probability one" is `∀ᵐ ω′ ∂P′`. -/
theorem theorem_11 {Ω Ξ Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
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
    (hG_law : P.map G = volume.restrict (Set.Icc (0 : ℝ) 1)) (r : ℕ → ℝ) (hr_nonneg : ∀ N, 0 ≤ r N) (hr : Tendsto r atTop (𝓝 0)) :
    (∀ᵐ ω' ∂P', Tendsto (fun N => optimalValue Zad (empiricalObjective ℛ G ξs f B φ N ω'))
        atTop (𝓝 (optimalValue Zad (trueObjective ℛ ξ f B φ)))) ∧
      (IsRFunction φ → ∀ᵐ ω' ∂P',
        Tendsto (fun N => CompositeSAA.excess (epsSolutionSet Zad (empiricalObjective ℛ G ξs f B φ N ω') (r N))
          (solutionSet Zad (trueObjective ℛ ξ f B φ))) atTop (𝓝 0)) := by sorry

end RiskAverseConsistency
