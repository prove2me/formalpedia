-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_eq_2_31
-- name    : UnifErgHW.Diffusion.eq_2_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:13.83129+00:00
-- url     : https://prove2.me/theorems/013e0a13-44b9-45ae-937a-afed3e8912ba
-- title:
--   (2.31), p. 10 — ½ trace(a∇²V) ≤ ε((3/2)(ε + θ) + εC̄)V under ∑λ̃_i/µ_i = 1
-- statement:
--   Let $\sigma=\mathrm{diag}(r_1,\dots,r_m)$, $a=\sigma\sigma^{\mathsf T}=\mathrm{diag}(2\tilde\lambda_i)$ with $\tilde\lambda_i=r_i^2/2$, and assume $\sum_i\tilde\lambda_i/\mu_i=1$. Let $\varepsilon>0$, $0<\theta\le1$, and $V=\exp(\Psi^*_{\varepsilon,\theta})$. Then for every $x\in\mathbb R^m$,
--   $$
--   \frac12\,\mathrm{trace}\big(a\nabla^2V(x)\big)\le\varepsilon\Big(\tfrac32(\varepsilon+\theta)+\varepsilon\bar C\Big)V(x),\qquad \bar C=\sum_i\frac{\tilde\lambda_i}{\mu_i^2}.
--   $$
--
--   Together with Lemma 2.1 at $c=\infty$ this bounds the full generator $\mathcal L_uV$; the bound is of order $\varepsilon(\varepsilon+\theta)V$, which is dominated by the drift term once $\varepsilon$ and $\theta$ are small.
--
--   **Formalization Note** The trace is written as $\frac12\sum_{i,j}(\sigma\sigma^{\mathsf T})_{ij}\,\partial_{ij}V(x)$, the second-order part of the generator used throughout the mission. The normalization $\sum_i\tilde\lambda_i/\mu_i=1$ is the identity the paper invokes "(see (3.1))"; it holds for Poisson arrivals.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 10, proof of Theorem 2.1, (2.31)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov

open MeasureTheory Matrix
open scoped NNReal ENNReal RealInnerProductSpace
open GPhNGIDiffusion.EMError (SolvesAdditiveSDE IsTransitionFunction IsInvariantMeasure generator tvNormWeighted cutoff partial2)

namespace UnifErgHW.Diffusion

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 10, (2.31) (proof of Theorem 2.1): with `σ = diag(2λ̃₁, …, 2λ̃_m)^{1/2}`, `a = σσᵀ`,
`∑ᵢλ̃ᵢ/µᵢ = 1`, `ε > 0` and `0 < θ ≤ 1`,
`½ trace(a∇²V(x)) ≤ ε((3/2)(ε + θ) + εC̄)V(x)` for all `x`, where `C̄ = ∑ᵢλ̃ᵢ/µᵢ²`.

Formalization Note. `σ = diag(r)`, so `λ̃ᵢ = rᵢ²/2` and `∑ᵢλ̃ᵢ/µᵢ = 1` is `IsNormalized D`. The trace
term is written exactly as the second-order part of the published `generator`:
`½∑ᵢ∑ⱼ(σσᵀ)ᵢⱼ ∂ᵢⱼV(x)`. The page's preceding identity for `½ trace(a∇²V)` is a proof step and is not
stated. -/
theorem eq_2_31 {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m) (hσ : IsNormalized D)
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (x : EthierKurtz.SDEState m) :
    (1 / 2) * ∑ i, ∑ j, (sigma D * (sigma D)ᵀ) i j * partial2 (lyapV D ε θ) i j x ≤
      ε * (3 / 2 * (ε + θ) + ε * ∑ i, (D.r i ^ 2 / 2) / D.mu i ^ 2) * lyapV D ε θ x := by sorry

end UnifErgHW.Diffusion
