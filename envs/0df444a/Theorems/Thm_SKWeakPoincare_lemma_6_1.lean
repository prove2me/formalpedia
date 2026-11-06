-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_6_1
-- name    : SKWeakPoincare.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:18.568086+00:00
-- url     : https://prove2.me/theorems/fe4d8ed6-76fd-4cde-9cfa-8a9dca3b8096
-- title:
--   Lemma 6.1 — weak Poincaré inequality from localization with path costs
-- statement:
--   Fix $T,L,C_0,r>0$. For $n\ge2$ let $\mu$ be a full-support law on $\{\pm1\}^n$ with posterior mean $m$, and let $\mathfrak e:[0,T]\times\mathbb R^n\to[0,4n]$ be jointly Borel with
--   $$
--   \|m(y_1)-m(y_2)\|_2\le L\|y_1-y_2\|_2+\sqrt{\mathfrak e(t;y_1)}+\sqrt{\mathfrak e(t;y_2)}\qquad(t\in[0,T],\ y_1,y_2\in\mathbb R^n).
--   $$
--   For the localization paths $Y^\omega$ of $\mu$, let $U(\omega)=\int_0^T\mathfrak e(t;Y^\omega_t)\,dt$ and $E(\omega)=\mathfrak e(T;Y^\omega_T)$, and assume
--   $$
--   P_{\omega\sim\gamma}\big[U(\omega)>C_0\log n\ \text{or}\ E(\omega)>C_0\log n\big]\le n^{-r}.
--   $$
--   Suppose $a_n,\delta_n\ge0$ satisfy $E_{\omega\sim\gamma}\big[\mathrm{Var}_{\mu_{Y^\omega_T}}[f]\big]\le a_n\mathcal E_\mu(f,f)+\delta_n\operatorname{osc}(f)^2$ for every $f:\{\pm1\}^n\to\mathbb R$.
--
--   Then there are constants $\Gamma>0$, depending only on $T,L$, and $C,B>0$, depending only on $T,L,C_0$, such that for every $n\ge2$, every $f$ and every $8n^{-r}\le s\le\frac12$,
--   $$
--   \mathrm{Var}_\mu[f]\le\big(1+Cn^Bs^{-\Gamma}\big)a_n\,\mathcal E_\mu(f,f)+\Big(s+\big(1+Cn^Bs^{-\Gamma}\big)\delta_n\Big)\operatorname{osc}(f)^2 .
--   $$
--   Here $\gamma$ is Wiener measure, $\mathcal E_\mu(f,f)=\frac1n\sum_iE_{X\sim\mu}\big[\mathrm{Var}_{X\sim\mu}[f(X)\mid X_{-i}]\big]$ is the Dirichlet form of random-scan heat-bath dynamics, and $\operatorname{osc}(f)=\max f-\min f$.
--
--   This criterion turns a posterior-variance bound at the end of localization into a weak Poincaré inequality for $\mu$ with polynomial constants.
--
--   **Formalization Note** $\Gamma$ is chosen before $C_0$ and $r$, and $C,B$ before $r$ and $n$. $U$ and $E$ are `pathCost T e (Y ω)` and `termCost T e (Y ω)`.
--
--   Differences from the source:
--   - encoding: Wiener measure γ and the localization paths Y^ω (ω ∈ C₀) → any γ with IsWienerMeasure T n γ, and a map Y with IsLocPath (postMean μ) ω (Y ω) for every path ω; reason: γ is unique; (8) has a unique solution for every continuous ω, so Y is the solution map
--   - encoding: 𝔢 : [0,T] × ℝⁿ → [0,4n] jointly Borel → IsCostFn T n e (Borel on ℝ × ℝⁿ, values in [0,4n] on [0,T]); reason: every Borel function on [0,T] × ℝⁿ extends to ℝ × ℝⁿ
--   - encoding: E_{ω∼γ}[Var_{μ_{Y^ω_T}}[f]] → the Bochner integral ∫ lawVar (tilt μ (Y ω)_T) f ∂γ; reason: the integrand is bounded by osc(f)² and measurable (the solution map is continuous, Lemma 3.4), so it is integrable and no default value 0 arises
--   - encoding: 𝓔_μ(f,f) and osc(f) → glauberDirichlet μ f and hMax f − hMin f; reason: glauberDirichlet is n⁻¹ Σᵢ E_μ[(f − Pᵢf)²], and Pᵢf = E_μ[f | X₋ᵢ]
--   - encoding: for each n ≥ 2 a law μ and numbers a_n, δ_n with the hypotheses; conclusion for every n ≥ 2 → the hypotheses and conclusion stated for each n ≥ 2 after Γ, C, B and r; reason: the constants are uniform in n, which is the source's quantifier order
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 6.1, p.37 (proof pp.39–40)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_gibbsOf
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKWeakPoincare_postMean
import Definitions.Def_SKWeakPoincare_PathSpace
import Definitions.Def_SKWeakPoincare_IsWienerMeasure
import Definitions.Def_SKWeakPoincare_IsCostFn

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory

namespace SKWeakPoincare

/-- **Lemma 6.1 (weak Poincaré inequality from localization).**
Hou–Liu–Yu, arXiv:2610.09882, Lemma 6.1, p. 37 (proof pp. 39–40).

Fix `T, L, C₀, r > 0`. For `n ≥ 2` let `μ` be a full-support distribution on `{±1}^n` with posterior
mean `m`, and `𝔢 : [0, T] × ℝ^n → [0, 4n]` jointly Borel with
`‖m(y₁) − m(y₂)‖₂ ≤ L‖y₁ − y₂‖₂ + √𝔢(t; y₁) + √𝔢(t; y₂)` for all `t ∈ [0, T]`, `y₁, y₂`. With the
localization paths `Y^ω` let `U(ω) = ∫₀ᵀ 𝔢(t; Y^ω_t) dt` and `E(ω) = 𝔢(T; Y^ω_T)`, and assume
`P_{ω∼γ}[U(ω) > C₀ log n or E(ω) > C₀ log n] ≤ n^{−r}`. Suppose `a_n, δ_n ≥ 0` satisfy
`E_{ω∼γ}[Var_{μ_{Y^ω_T}}[f]] ≤ a_n 𝓔_μ(f, f) + δ_n osc(f)²` for every `f`. Then there are `Γ > 0`
depending only on `T, L`, and `C, B > 0` depending only on `T, L, C₀`, such that for every `n ≥ 2`,
every `f` and every `8n^{−r} ≤ s ≤ 1/2`,
`Var_μ[f] ≤ (1 + Cn^B s^{−Γ}) a_n 𝓔_μ(f, f) + (s + (1 + Cn^B s^{−Γ}) δ_n) osc(f)²`.

**Formalization Note.** Quantifier order: `Γ` before `C₀` and `r`; `C, B` before `r` and `n`. `γ` is
Wiener measure (`IsWienerMeasure`); `Y` is the localization map (`IsLocPath (postMean μ) ω (Y ω)` for
every path); `U = pathCost T e`, `E = termCost T e`. `𝓔_μ` is the random-scan heat-bath Dirichlet form
`n⁻¹ Σᵢ E_μ[Var_μ(f | X₋ᵢ)]` (`glauberDirichlet`), `osc(f) = hMax f − hMin f`, `μ_y = tilt μ y`.
The expectation over `γ` of the bounded measurable `ω ↦ Var_{μ_{Y^ω_T}}[f]` is a Bochner integral. -/
theorem lemma_6_1 (T L : ℝ) (hT : 0 < T) (hL : 0 < L) :
    ∃ Γ : ℝ, 0 < Γ ∧ ∀ C₀ : ℝ, 0 < C₀ → ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
      ∀ r : ℝ, 0 < r → ∀ n : ℕ, 2 ≤ n → ∀ μ : Spin n → ℝ, IsFullSupportLaw μ →
      ∀ e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ, IsCostFn T n e → HasLipCost T L (postMean μ) e →
      ∀ Y : PathSpace T n → PathSpace T n, (∀ ω, IsLocPath (postMean μ) ω (Y ω)) →
      ∀ γ : Measure (PathSpace T n), IsWienerMeasure T n γ →
      γ {ω | C₀ * Real.log n < pathCost T e (Y ω) ∨ C₀ * Real.log n < termCost T e (Y ω)}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-r)) →
      ∀ a δ : ℝ, 0 ≤ a → 0 ≤ δ →
      (∀ f : Spin n → ℝ, ∫ ω, lawVar (tilt μ (WithLp.ofLp (pathExt (Y ω) T))) f ∂γ ≤
          a * glauberDirichlet μ f + δ * (hMax f - hMin f) ^ 2) →
      ∀ (f : Spin n → ℝ) (s : ℝ), 8 * (n : ℝ) ^ (-r) ≤ s → s ≤ 1 / 2 →
        lawVar μ f ≤ (1 + C * (n : ℝ) ^ B * s ^ (-Γ)) * a * glauberDirichlet μ f +
          (s + (1 + C * (n : ℝ) ^ B * s ^ (-Γ)) * δ) * (hMax f - hMin f) ^ 2 := by sorry

end SKWeakPoincare
