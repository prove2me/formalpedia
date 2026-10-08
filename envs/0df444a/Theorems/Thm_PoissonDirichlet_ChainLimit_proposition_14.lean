-- Prove2me | Theorems.Thm_PoissonDirichlet_ChainLimit_proposition_14
-- name    : PoissonDirichlet.ChainLimit.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:52.053791+00:00
-- url     : https://prove2.me/theorems/e7b75cbb-6b7e-4961-9533-bff1c18a6eb4
-- title:
--   Proposition 14, (42)–(43): PD(α, θ) as a local-time tilt of PD(α, 0)
-- statement:
--   Let $0<\alpha<1$ and $\theta> -\alpha$. Let $V^{(0)}$ and $V^{(\theta)}$ have laws $\mathrm{PD}(\alpha,0)$ and $\mathrm{PD}(\alpha,\theta)$, possibly on different probability spaces. Under the first law let $L=\lim_{n\to\infty} n(V_n^{(0)})^\alpha$. The local time is positive almost surely, $L^{\theta/\alpha}$ is integrable, and for every nonnegative product-measurable $f$,
--   $$\mathbb E_{\alpha,\theta}[f(V^{(\theta)})]=C_{\alpha,\theta}\,\mathbb E_{\alpha,0}[L^{\theta/\alpha}f(V^{(0)})],\qquad C_{\alpha,\theta}=\frac{1}{\mathbb E_{\alpha,0}[L^{\theta/\alpha}]}=\frac{\Gamma(\theta+1)\Gamma(1-\alpha)^{\theta/\alpha}}{\Gamma(\theta/\alpha+1)}.$$
--   The density transfers almost-sure events from $\mathrm{PD}(\alpha,0)$ to $\mathrm{PD}(\alpha,\theta)$.
--
--   **Formalization Note** The nonnegative expectations use extended nonnegative integrals, so an unbounded $f$ is allowed. The displayed finite normalizing expectation uses a Bochner integral; its integrability is included in the conclusion. The local-time limit is a hypothesis identifying $L$, as in (24), not an independently chosen weight. The paper cites [51, Corollary 3.15] for this proposition.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 865, Proposition 14, (42)–(43)

import Mathlib
import Definitions.Def_PoissonDirichlet_ChainLimit_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.ChainLimit

/-- Proposition 14, (42)–(43), p. 865. `L₀` is tied to the limit (24).
The integrability and positivity clauses spell out the finiteness and positive
local time implicit in the paper's normalizing expectation. -/
theorem proposition_14 (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (V₀ : Ω₀ → ℕ → ℝ) (hV₀ : HasPD α 0 P₀ V₀) (L₀ : Ω₀ → ℝ)
    (hL₀ : ∀ᵐ ω ∂P₀,
      Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V₀ ω k ^ α) atTop (𝓝 (L₀ ω)))
    {Ω₁ : Type*} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (V₁ : Ω₁ → ℕ → ℝ) (hV₁ : HasPD α θ P₁ V₁) :
    (∀ᵐ ω ∂P₀, 0 < L₀ ω) ∧
    Integrable (fun ω => L₀ ω ^ (θ / α)) P₀ ∧
    (∀ f : (ℕ → ℝ) → ENNReal, Measurable f →
      ∫⁻ ω, f (V₁ ω) ∂P₁ =
        ENNReal.ofReal (pdConst α θ) *
          ∫⁻ ω, ENNReal.ofReal (L₀ ω ^ (θ / α)) * f (V₀ ω) ∂P₀) ∧
    pdConst α θ = 1 / ∫ ω, L₀ ω ^ (θ / α) ∂P₀ := by sorry

end PoissonDirichlet.ChainLimit
