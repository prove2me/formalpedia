-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_proposition_14
-- name    : PoissonDirichlet.Chain.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:25.211128+00:00
-- url     : https://prove2.me/theorems/dab81b16-7cef-4b37-b8bd-b419c27af8b1
-- title:
--   Proposition 14, p. 865 — PD(α, θ) has density C_{α,θ} L^{θ/α} with respect to PD(α, 0)
-- statement:
--   Let $0 < \alpha < 1$ and $\theta > -\alpha$. Let $P_{\alpha,0}$ govern $(V_n)$ with the $\mathrm{PD}(\alpha,0)$ law and let $L = \lim_{n\to\infty} n V_n^\alpha$ be its local time (24). Let $P_{\alpha,\theta}$ govern a sequence with the $\mathrm{PD}(\alpha,\theta)$ law. For every nonnegative product measurable function $f$,
--   $$E_{\alpha,\theta}[f(V_1, V_2, \dots)] = C_{\alpha,\theta}\,E_{\alpha,0}[L^{\theta/\alpha} f(V_1, V_2, \dots)], \qquad (42)$$
--   where
--   $$C_{\alpha,\theta} = \frac{1}{E_{\alpha,0}(L^{\theta/\alpha})} = \frac{\Gamma(\theta+1)}{\Gamma(\theta/\alpha+1)}\,\Gamma(1-\alpha)^{\theta/\alpha}. \qquad (43)$$
--
--   This absolute continuity relation is the first step (142) of the proof of Theorem 38 (i).
--
--   **Formalization Note.** The two laws live on two probability spaces. $L$ is a random variable given together with its defining almost sure limit (24). The paper quotes this proposition from [51], Corollary 3.15.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 865, Proposition 14, (42), (43)

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- Proposition 14, p. 865 (quoted from [51], Corollary 3.15): for `0 < α < 1`, `θ > -α`,
`E_{α,θ}[f(V)] = C_{α,θ} E_{α,0}[L^{θ/α} f(V)]` for every nonnegative product-measurable `f`,
where `L = lim n V_n^α` (24) under `PD(α, 0)`; and (43), `C_{α,θ} = 1 / E_{α,0}(L^{θ/α})`. -/
theorem proposition_14 (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (V₀ : Ω₀ → ℕ → ℝ) (hV₀ : PoissonDirichlet.Ratio.HasPD α 0 P₀ V₀) (L₀ : Ω₀ → ℝ)
    (hL₀ : ∀ᵐ ω ∂P₀, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V₀ ω k ^ α) atTop (𝓝 (L₀ ω)))
    {Ω₁ : Type*} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (V₁ : Ω₁ → ℕ → ℝ) (hV₁ : PoissonDirichlet.Ratio.HasPD α θ P₁ V₁) :
    (∀ f : (ℕ → ℝ) → ENNReal, Measurable f →
      ∫⁻ ω, f (V₁ ω) ∂P₁ =
        ENNReal.ofReal (PoissonDirichlet.Moments.pdConst α θ) * ∫⁻ ω, ENNReal.ofReal (L₀ ω ^ (θ / α)) * f (V₀ ω) ∂P₀) ∧
    PoissonDirichlet.Moments.pdConst α θ = 1 / ∫ ω, L₀ ω ^ (θ / α) ∂P₀ := by sorry

end PoissonDirichlet.Chain
