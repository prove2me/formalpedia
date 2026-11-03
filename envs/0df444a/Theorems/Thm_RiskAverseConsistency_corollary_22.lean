-- Prove2me | Theorems.Thm_RiskAverseConsistency_corollary_22
-- name    : RiskAverseConsistency.corollary_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:23:34.014927+00:00
-- url     : https://prove2.me/theorems/8aba00a7-ce70-4b9f-84aa-1ca2e1ebcbcf
-- title:
--   Corollary 22 — almost sure Mosco-epiconvergence of composed empirical risks
-- statement:
--   Let $Y_0\subset Y$ be a closed subset of a separable Banach space $Y$ and $W_0$ a nonempty, closed, convex subset of a reflexive, separable Banach space $W$. Let the hypotheses of Theorem 21 hold with $V=Y_0$, and let $\mathbf B:W\to Y$ be linear and completely continuous with $\mathbf B(W_0)\subset Y_0$. Then, for $P'$-almost every $\omega'$,
--
--   $$
--   \hat\phi_N\circ\mathbf B:W_0\to\mathbb R\ \text{ Mosco-epiconverges to }\ \phi\circ\mathbf B:W_0\to\mathbb R\qquad(N\to\infty).
--   $$
--
--   In the proof of Theorem 11 this is applied with $\Psi=f$, $\zeta=\xi$ and $W_0=Z_{\mathrm{ad}}$.
--
--   Differences from the source:
--   - encoding: Theorem 21 applied with V = Y₀ to Ψ : Y₀ × Θ → ℝ → Ψ : Y → Θ → ℝ and Assumption 20 for the subtype Y₀ (with the restricted Borel σ-algebra) and the restriction of Ψ; reason: Lean convention; the restricted Borel σ-algebra of Y is the Borel σ-algebra of Y₀, and values off Y₀ are never used since B(W₀) ⊂ Y₀
--   - encoding: B : Z → Y linear and completely continuous → B : Z →ₗ[ℝ] Y with CompletelyContinuousOn univ B; reason: same instances; no boundedness is added
--   - encoding: a fixed G : Ω → [0, 1] with uniform distribution ν (exists since P is nonatomic) → every measurable G : Ω → ℝ with P.map G = Lebesgue measure on [0, 1]; reason: such G takes values in [0, 1] almost surely, and the paper's statements do not depend on which G is chosen
--   - encoding: samples ξ¹, …, ξᴺ, N ∈ ℕ = {1, 2, …} → samples ξs 0, …, ξs (N−1); N ranges over ℕ including 0; reason: index shift; only N → ∞ enters the statement
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.16, Corollary 22

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_RiskAverseConsistency_Assumption20
import Definitions.Def_RiskAverseConsistency_IsConvexRiskMeasure
import Definitions.Def_RiskAverseConsistency_IsLawInvariant
import Definitions.Def_RiskAverseConsistency_riskOf
import Definitions.Def_RiskAverseConsistency_empiricalRisk
import Definitions.Def_RiskAverseConsistency_MoscoConvergesOn
import Definitions.Def_RiskAverseConsistency_CompletelyContinuousOn

open MeasureTheory QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- **Corollary 22.** Let `Y₀ ⊂ Y` be a closed subset of a separable Banach space `Y` and `W₀` a
nonempty, closed, convex subset of a reflexive, separable Banach space `W`. Let the hypotheses of
Theorem 21 hold with `V = Y₀`. Suppose `B : W → Y` is linear and completely continuous with
`B(W₀) ⊂ Y₀`. Then `φ̂_N ∘ B : W₀ → ℝ` Mosco-epiconverges to `φ ∘ B : W₀ → ℝ` with probability one as
`N → ∞`.

Milz, Surowiec, arXiv:2207.14756v2, Corollary 22, p.16.

Formalization Note: `Ψ` is a function on `Y × Θ`; "the hypotheses of Theorem 21 with `V = Y₀`" is
Assumption 20 for the metric space `Y₀` (subtype, with the Borel σ-algebra of `Y` restricted, which
is the Borel σ-algebra of `Y₀`) and the restriction of `Ψ` to `Y₀ × Θ`, plus `ρ` law invariant and
convex. `φ̂_N(y, ω′) = ρ(Ĥ⁻¹_{y,N}(G(·); ω′))` and `φ(y) = ρ(Ψ_y(ζ))` are the functions of Theorem 21,
cast to `EReal`; Mosco-epiconvergence is `MoscoConvergesOn W₀`, for `P′`-almost every `ω′`. The
uniform `G` is any measurable `G : Ω → ℝ` with law Lebesgue measure on `[0,1]`. -/
theorem corollary_22 {Ω Θ Ω' Y W : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace Ω'] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [TopologicalSpace.SeparableSpace W] (hW : IsReflexive W) {Y₀ : Set Y} (hY₀ : IsClosed Y₀)
    {W₀ : Set W} (hW₀_ne : W₀.Nonempty) (hW₀_closed : IsClosed W₀) (hW₀_convex : Convex ℝ W₀)
    (P : Measure Ω) (𝕄 : Measure Θ) (ζ : Ω → Θ) (P' : Measure Ω') (ζs : ℕ → Ω' → Θ)
    {p : ENNReal} (Ψ : Y → Θ → ℝ) (hA : Assumption20 P 𝕄 ζ P' ζs p (fun (y : Y₀) θ => Ψ y θ))
    (ρ : Lp ℝ p P → ℝ) (hρ_convex : IsConvexRiskMeasure ρ) (hρ_law : IsLawInvariant ρ)
    (G : Ω → ℝ) (hG_meas : Measurable G)
    (hG_law : P.map G = volume.restrict (Set.Icc (0 : ℝ) 1)) (B : W →ₗ[ℝ] Y)
    (hB : CompletelyContinuousOn Set.univ B) (hBW₀ : Set.MapsTo B W₀ Y₀) :
    ∀ᵐ ω' ∂P', MoscoConvergesOn W₀
      (fun N w => ((empiricalRisk ρ G (fun i => Ψ (B w) (ζs i ω')) N : ℝ) : EReal))
      (fun w => ((riskOf ρ (fun ω => Ψ (B w) (ζ ω)) : ℝ) : EReal)) := by sorry

end RiskAverseConsistency
