-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_proposition_14
-- name    : PoissonDirichlet.Moments.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:52.907625+00:00
-- url     : https://prove2.me/theorems/5efe3074-9667-4731-84ac-312e37db23f1
-- title:
--   Proposition 14, p. 865 — PD(α, θ) has density C_{α,θ}L^{θ/α} with respect to PD(α, 0); (42)–(43)
-- statement:
--   Let $0<\alpha<1$ and $\theta>-\alpha$. Let $(V_n)$ have the $\mathrm{PD}(\alpha,\theta)$ law under $P_{\alpha,\theta}$, and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ law under $P_{\alpha,0}$, with local time $L=\lim_{n\to\infty}nV_n^\alpha$ (24). Then for every nonnegative product measurable function $f$,
--
--   $$E_{\alpha,\theta}\big[f(V_1,V_2,\dots)\big]=C_{\alpha,\theta}\,E_{\alpha,0}\big[L^{\theta/\alpha}f(V_1,V_2,\dots)\big],$$
--
--   and
--
--   $$C_{\alpha,\theta}=\frac{1}{E_{\alpha,0}(L^{\theta/\alpha})}=\frac{\Gamma(\theta+1)}{\Gamma(\theta/\alpha+1)}\Gamma(1-\alpha)^{\theta/\alpha}.$$
--
--   So $\mathrm{PD}(\alpha,\theta)$ is absolutely continuous with respect to $\mathrm{PD}(\alpha,0)$ with density a constant times $L^{\theta/\alpha}$. It reduces every $\mathrm{PD}(\alpha,\theta)$ computation of the paper to $\mathrm{PD}(\alpha,0)$; in particular it turns Lemma 27 into Proposition 17.
--
--   **Formalization Note** The two laws live on two probability spaces. $C_{\alpha,\theta}$ is defined by its Gamma expression, so the first equality in (43) is a genuine claim. The paper quotes this result from Perman, Pitman and Yor [51], Corollary 3.15, and does not prove it. $L$ enters only through its defining limit (24).
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 865, Proposition 14, (42), (43)

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

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
        ENNReal.ofReal (pdConst α θ) * ∫⁻ ω, ENNReal.ofReal (L₀ ω ^ (θ / α)) * f (V₀ ω) ∂P₀) ∧
    pdConst α θ = 1 / ∫ ω, L₀ ω ^ (θ / α) ∂P₀ := by sorry

end PoissonDirichlet.Moments
