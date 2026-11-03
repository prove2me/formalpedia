-- Prove2me | Theorems.Thm_RiskAverseConsistency_theorem_23
-- name    : RiskAverseConsistency.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:05.405658+00:00
-- url     : https://prove2.me/theorems/e6e8e42b-26bc-4c80-baaa-eab77e16b213
-- title:
--   Theorem 23 — strong consistency of plug-in risk estimators
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be complete and nonatomic, $1\le p<\infty$, and $\rho:L^p(\Omega,\mathcal F,P)\to\mathbb R$ a law invariant, convex risk measure. Let $X\in L^p(\Omega,\mathcal F,P)$ and let $X_1,X_2,\dots$, defined on a complete probability space $(\Omega',\mathcal F',P')$, be i.i.d. real random variables each distributed as $X$. Let $\hat H_N(\cdot;\omega')$ be the empirical distribution function of $X_1(\omega'),\dots,X_N(\omega')$ and $\hat H_N^{-1}(\cdot;\omega')$ its quantile function. Then, with $G:\Omega\to[0,1]$ uniform,
--
--   $$
--   \rho(\hat H_N)=\rho\bigl(\hat H_N^{-1}(G(\cdot);\omega')\bigr)\ \longrightarrow\ \rho(X)\qquad\text{as }N\to\infty
--   $$
--
--   for $P'$-almost every $\omega'$.
--
--   The paper attributes this result to [66, Thm. 2.1] and [68, Thm. 9.65]; it is the pointwise law of large numbers from which the epigraphical one (Theorem 21) is built.
--
--   Differences from the source:
--   - encoding: ℛ applied to elements of Lᵖ(Ω, F, P) (F(Bz), Ĥ⁻¹(G(·))) → riskOf ℛ X = ℛ of the Lᵖ class of X when X ∈ Lᵖ, junk 0 otherwise; reason: every argument used is in Lᵖ (proved in the verification file), so the junk branch never fires
--   - encoding: a fixed G : Ω → [0, 1] with uniform distribution ν (exists since P is nonatomic) → every measurable G : Ω → ℝ with P.map G = Lebesgue measure on [0, 1]; reason: such G takes values in [0, 1] almost surely, and the paper's statements do not depend on which G is chosen
--   - encoding: samples ξ¹, …, ξᴺ, N ∈ ℕ = {1, 2, …} → samples ξs 0, …, ξs (N−1); N ranges over ℕ including 0; reason: index shift; only N → ∞ enters the statement
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.17, Theorem 23 (setting on pp.16–17)

import Mathlib
import Definitions.Def_RiskAverseConsistency_IsNonatomic
import Definitions.Def_RiskAverseConsistency_IsConvexRiskMeasure
import Definitions.Def_RiskAverseConsistency_IsLawInvariant
import Definitions.Def_RiskAverseConsistency_riskOf
import Definitions.Def_RiskAverseConsistency_empiricalRisk

open MeasureTheory Filter Topology

namespace RiskAverseConsistency

/-- **Theorem 23** (consistency of plug-in risk estimators). Let `X ∈ Lᵖ(Ω, F, P)` and let
`X₁, X₂, …`, defined on a complete probability space `(Ω′, F′, P′)`, be independent identically
distributed real random variables each with the distribution of `X`; let `Ĥ_N(·; ω′)` be the
empirical distribution function of `X₁(ω′), …, X_N(ω′)` and `Ĥ⁻¹_N(·; ω′)` its quantile function.
If `(Ω, F, P)` is complete and nonatomic, `1 ≤ p < ∞`, and `ρ : Lᵖ(Ω, F, P) → ℝ` is a law
invariant, convex risk measure, then `ρ(Ĥ_N) = ρ(Ĥ⁻¹_N(G(·)))` converges to `ρ(X)` with probability
one as `N → ∞`.

Milz, Surowiec, arXiv:2207.14756v2, Theorem 23, p.17 (setting on pp.16–17).

Formalization Note: `X` is a function `Ω → ℝ` with `X ∈ Lᵖ` (`MemLp`), and `ρ(X)` is `riskOf ρ X`.
The samples are `Xs 0, Xs 1, …`. The uniform `G : Ω → [0,1]` of §2.1 is any measurable
`G : Ω → ℝ` whose law is Lebesgue measure on `[0,1]`, and the statement holds for each such `G`. -/
theorem theorem_23 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP_complete : P.IsComplete) (hP_nonatomic : IsNonatomic P)
    {p : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (ρ : Lp ℝ p P → ℝ)
    (hρ_convex : IsConvexRiskMeasure ρ) (hρ_law : IsLawInvariant ρ) (X : Ω → ℝ)
    (hX : MemLp X p P) (P' : Measure Ω') [IsProbabilityMeasure P'] (hP'_complete : P'.IsComplete)
    (Xs : ℕ → Ω' → ℝ) (hXs_meas : ∀ i, Measurable (Xs i))
    (hXs_indep : ProbabilityTheory.iIndepFun Xs P') (hXs_law : ∀ i, P'.map (Xs i) = P.map X)
    (G : Ω → ℝ) (hG_meas : Measurable G)
    (hG_law : P.map G = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    ∀ᵐ ω' ∂P', Tendsto (fun N => empiricalRisk ρ G (fun i => Xs i ω') N) atTop
      (𝓝 (riskOf ρ X)) := by sorry

end RiskAverseConsistency
