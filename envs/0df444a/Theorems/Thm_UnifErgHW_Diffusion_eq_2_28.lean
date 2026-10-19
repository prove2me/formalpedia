-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_eq_2_28
-- name    : UnifErgHW.Diffusion.eq_2_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:08.825291+00:00
-- url     : https://prove2.me/theorems/19ee4a91-0ae1-4e70-bc42-1e9ace840536
-- title:
--   Theorem 2.1(a), (2.28), p. 10 — uniform Foster–Lyapunov equation L_uV ≤ κ_0 − ε(ϱ/(2m) + (θ/2)‖x^−‖_1)V (corrected)
-- statement:
--   Assume the centred drift with spare capacity $\varrho>0$, the normalization $\sum_i r_i^2/(2\mu_i)=1$, condition (2.15) $\theta(\beta_{\max}-1)^+\le1$, and
--   $$
--   0<\theta\le\frac{\varrho}{3m(2\varrho+m)} .
--   $$
--   Then there is $\varepsilon_0>0$ such that for every $0<\varepsilon\le\varepsilon_0$ there is a constant $\kappa_0>0$ with
--   $$
--   \mathcal L_uV(x)\le\kappa_0-\varepsilon\Big(\frac{\varrho}{2m}+\frac{\theta}{2}\|x^-\|_1\Big)V(x)\qquad\forall\,(x,u)\in\mathbb R^m\times\Delta,
--   $$
--   where $V=\exp(\Psi^*_{\varepsilon,\theta})$ and $\mathcal L_uf=\frac12\mathrm{trace}(a\nabla^2f)+\langle b(\cdot,u),\nabla f\rangle$ is the generator (2.7).
--
--   This is the Foster–Lyapunov equation, uniform over all control values, from which positive recurrence and exponential ergodicity under every Markov control follow.
--
--   **Formalization Note** The paper prints the coefficient $\theta$ in front of $\|x^-\|_1$. That version is false: along $x=-Re$ with $R\ge1/\varepsilon$ one gets $\mathcal L_uV+\varepsilon(\frac{\varrho}{2m}+\theta\|x^-\|_1)V=\varepsilon(\theta\varrho+\frac{\varrho}{2m}+\varepsilon\theta^2\bar C)V\to\infty$. Any coefficient smaller than $\theta$ works; $\theta/2$ is stated. The rest of Theorem 2.1 uses only $\mathcal L_uV\le\kappa_0-\frac{\varepsilon\varrho}{2m}V$ and is unaffected. The normalization is the identity used in (2.31). (2.15) is written coordinatewise.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 10, Theorem 2.1(a), (2.28)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov

open MeasureTheory
open scoped NNReal ENNReal RealInnerProductSpace
open GPhNGIDiffusion.EMError (SolvesAdditiveSDE IsTransitionFunction IsInvariantMeasure generator tvNormWeighted cutoff partial2)

namespace UnifErgHW.Diffusion

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 10, Theorem 2.1(a), (2.28), with the coefficient of `‖x⁻‖₁` corrected from `θ` to
`θ/2`: assume `ϱ > 0`, (2.15) and `0 < θ ≤ ϱ/(3m(2ϱ + m))` (2.27). There is `ε₀ > 0` such that for
each `0 < ε ≤ ε₀` there is `κ₀ > 0` with
`L_uV(x) ≤ κ₀ − ε(ϱ/(2m) + (θ/2)‖x⁻‖₁)V(x)` for all `(x, u) ∈ ℝ^m × ∆`.

Formalization Note. As printed (coefficient `θ`) the inequality is false: along `x = −Re`,
`R ≥ 1/ε`, one has `L_uV + ε(ϱ/(2m) + θ‖x⁻‖₁)V = ε(θϱ + ϱ/(2m) + εθ²C̄)V → ∞`. Any coefficient
`< θ` works; `θ/2` is posed. `L_u` is the published `generator` with drift `b(·, u)` and
`σ = diag(r)`, i.e. (2.7). The drift is centred (`IsCentered`, Remark 2.3) and `∑ᵢrᵢ²/(2µᵢ) = 1`
(`IsNormalized`, the normalization `∑λ̃ᵢ/µᵢ = 1` used in (2.31)). (2.15) is written
`∀ i, θ(βᵢ − 1)⁺ ≤ 1`. -/
theorem eq_2_28 {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m) (ϱ θ : ℝ)
    (hℓ : IsCentered D ϱ) (hϱ : 0 < ϱ) (hσ : IsNormalized D)
    (h215 : ∀ i, θ * max (D.theta i / D.mu i - 1) 0 ≤ 1)
    (hθ : 0 < θ) (h227 : θ ≤ ϱ / (3 * m * (2 * ϱ + m))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), u ∈ stdSimplex ℝ (Fin m) →
        generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x
          ≤ κ₀ - ε * (ϱ / (2 * m) + θ / 2 * negL1 x) * lyapV D ε θ x := by sorry

end UnifErgHW.Diffusion
