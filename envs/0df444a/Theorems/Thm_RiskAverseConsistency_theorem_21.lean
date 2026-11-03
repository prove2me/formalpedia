-- Prove2me | Theorems.Thm_RiskAverseConsistency_theorem_21
-- name    : RiskAverseConsistency.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:19.762948+00:00
-- url     : https://prove2.me/theorems/5e39a243-7cdb-4081-9639-0384f08326a4
-- title:
--   Theorem 21 — epigraphical law of large numbers for law invariant risk functionals
-- statement:
--   Let Assumption 20 hold, let $\rho:L^p(\Omega,\mathcal F,P)\to\mathbb R$ be a law invariant, convex risk measure and $G:\Omega\to[0,1]$ uniformly distributed. For $v\in V$ let $\hat H_{v,N}(\cdot;\omega')$ be the empirical distribution function of $\Psi(v,\zeta^1(\omega')),\dots,\Psi(v,\zeta^N(\omega'))$, and define
--
--   $$
--   \hat\phi_N(v,\omega'):=\rho\bigl(\hat H^{-1}_{v,N}(G(\cdot);\omega')\bigr),\qquad \phi(v):=\rho(\Psi_v(\zeta)).
--   $$
--
--   Then $\phi$ is lower semicontinuous and finite-valued, and for $P'$-almost every $\omega'$ the sequence $\hat\phi_N(\cdot,\omega')$ epiconverges to $\phi$ on $V$ as $N\to\infty$.
--
--   This extends [66, Thm. 3.1] from $\mathbb R^n$ to complete separable metric spaces.
--
--   Differences from the source:
--   - encoding: φ is finite-valued → φ is ℝ-valued, so finiteness holds by typing; reason: Lean convention; the conclusion keeps lower semicontinuity as a separate conjunct
--   - encoding: a fixed G : Ω → [0, 1] with uniform distribution ν (exists since P is nonatomic) → every measurable G : Ω → ℝ with P.map G = Lebesgue measure on [0, 1]; reason: such G takes values in [0, 1] almost surely, and the paper's statements do not depend on which G is chosen
--   - encoding: samples ξ¹, …, ξᴺ, N ∈ ℕ = {1, 2, …} → samples ξs 0, …, ξs (N−1); N ranges over ℕ including 0; reason: index shift; only N → ∞ enters the statement
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.16, Theorem 21 (definitions of $\hat\phi_N$, $\phi$ on p.16)

import Mathlib
import Definitions.Def_RiskAverseConsistency_Assumption20
import Definitions.Def_RiskAverseConsistency_IsConvexRiskMeasure
import Definitions.Def_RiskAverseConsistency_IsLawInvariant
import Definitions.Def_RiskAverseConsistency_riskOf
import Definitions.Def_RiskAverseConsistency_empiricalRisk
import Definitions.Def_RiskAverseConsistency_EpiConvergesOn

open MeasureTheory

namespace RiskAverseConsistency

/-- **Theorem 21** (epigraphical law of large numbers for law invariant risk functionals). If
Assumption 20 holds and `ρ : Lᵖ(Ω, F, P) → ℝ` is a law invariant, convex risk measure, then
`φ(v) := ρ(Ψ_v(ζ))` is lower semicontinuous and finite-valued, and `φ̂_N(v, ω′) :=
ρ(Ĥ⁻¹_{v,N}(G(·); ω′))` epiconverges to `φ` with probability one as `N → ∞`, where `Ĥ_{v,N}(·; ω′)` is
the empirical distribution function of `Ψ(v, ζ¹(ω′)), …, Ψ(v, ζᴺ(ω′))`.

Milz, Surowiec, arXiv:2207.14756v2, Theorem 21, p.16 (definitions of `φ̂_N`, `φ` on p.16).

Formalization Note: `φ` and `φ̂_N` are real-valued, so "finite-valued" holds by typing; lower
semicontinuity is the first conjunct. Epiconvergence (Definition 2, on the whole complete metric
space `V`) is `EpiConvergesOn univ` of the `EReal` casts, for `P′`-almost every `ω′`. The uniform
`G : Ω → [0,1]` is any measurable `G : Ω → ℝ` whose law is Lebesgue measure on `[0,1]`, and the
statement holds for each such `G`. Samples are indexed from `0`. -/
theorem theorem_21 {Ω Θ Ω' V : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace Ω'] [MetricSpace V] [MeasurableSpace V] [BorelSpace V]
    (P : Measure Ω) (𝕄 : Measure Θ) (ζ : Ω → Θ) (P' : Measure Ω') (ζs : ℕ → Ω' → Θ)
    {p : ENNReal} (Ψ : V → Θ → ℝ) (hA : Assumption20 P 𝕄 ζ P' ζs p Ψ) (ρ : Lp ℝ p P → ℝ)
    (hρ_convex : IsConvexRiskMeasure ρ) (hρ_law : IsLawInvariant ρ) (G : Ω → ℝ)
    (hG_meas : Measurable G) (hG_law : P.map G = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    LowerSemicontinuous (fun v => riskOf ρ (fun ω => Ψ v (ζ ω))) ∧
      ∀ᵐ ω' ∂P', EpiConvergesOn Set.univ
        (fun N v => ((empiricalRisk ρ G (fun i => Ψ v (ζs i ω')) N : ℝ) : EReal))
        (fun v => ((riskOf ρ (fun ω => Ψ v (ζ ω)) : ℝ) : EReal)) := by sorry

end RiskAverseConsistency
