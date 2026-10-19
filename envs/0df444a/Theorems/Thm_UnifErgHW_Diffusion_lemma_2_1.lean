-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_lemma_2_1
-- name    : UnifErgHW.Diffusion.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:16.322686+00:00
-- url     : https://prove2.me/theorems/f0bc9016-f5b8-4c83-bdba-974c5aa208a4
-- title:
--   Lemma 2.1, p. 8 — drift inequalities (2.17) for ⟨∇V, b_c⟩ on K^−_0 and on K^+_0 × ∆
-- statement:
--   Let $\varrho>0$ and let $\theta>0$ satisfy $\theta(\beta_{\max}-1)^+\le 1$ (2.15), where $\beta_i=\gamma_i/\mu_i$. Let $\varepsilon>0$, let $V=\exp(\varepsilon\theta\Psi(-x)+\Psi_\varepsilon(x))$ as in (2.16), and for $c\in[1,\infty]$ let $b_c$ be the truncated drift (2.14). Write $K^-_0=\{x:\langle e,x\rangle\le 0\}$ and $K^+_0=\{x:\langle e,x\rangle\ge 0\}$. Then
--   $$
--   \big\langle\nabla V(x),b_c(x,u)\big\rangle\le
--   \begin{cases}
--   \varepsilon\Big(\theta\varrho+\dfrac{m}{2\varepsilon}(1+\varepsilon\theta)-(\theta\wedge1)\|x\|_1\Big)V(x), & x\in K^-_0,\\[2mm]
--   -\varepsilon\Big(\dfrac{\varrho}{m}-\theta\varrho-\theta\dfrac{m}{2}+\theta\|x^-\|_1\Big)V(x), & (x,u)\in K^+_0\times\Delta .
--   \end{cases}
--   $$
--
--   With $c=\infty$ this is the drift part of the Foster–Lyapunov equation (2.28); finite $c$ is used for the prelimit queues of Section 3.
--
--   **Formalization Note** On $K^-_0$ we have $\langle e,x\rangle^+=0$, so $b_c(x,u)$ does not depend on $u$ and the first bound is stated for every $u$. Condition (2.15) is written as $\theta(\beta_i-1)^+\le1$ for every $i$, which is equivalent because $\theta>0$. No smallness of $\varepsilon$ is assumed, as in the paper. $c$ is an extended real with $1\le c$; $c=\top$ is $c=\infty$.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 8, Lemma 2.1 with (2.14)–(2.17)

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

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 8, Lemma 2.1 with (2.14): assume `ϱ > 0` and `θ > 0` with `θ(β_max − 1)⁺ ≤ 1` (2.15).
Then for every `ε > 0` and every `c ∈ [1, ∞]`, `V = exp(Ψ*_{ε,θ})` (2.16) satisfies (2.17):
`⟨∇V(x), b_c(x,u)⟩ ≤ ε(θϱ + m/(2ε)(1 + εθ) − (θ ∧ 1)‖x‖₁)V(x)` for `x ∈ K⁻₀`, and
`⟨∇V(x), b_c(x,u)⟩ ≤ −ε(ϱ/m − θϱ − θm/2 + θ‖x⁻‖₁)V(x)` for `(x, u) ∈ K⁺₀ × ∆`.

Formalization Note. `b_c` is `driftTrunc D ϱ c` with `c : EReal`, `1 ≤ c` (`c = ⊤` is `c = ∞`).
`K⁻₀ = {∑ᵢxᵢ ≤ 0}` and `K⁺₀ = {∑ᵢxᵢ ≥ 0}` (Definition 2.1 with δ = 0). On `K⁻₀` we have
`⟨e,x⟩⁺ = 0`, so `b_c(x, u)` does not depend on `u` and the first bound is stated for every `u`.
(2.15) is written `∀ i, θ(βᵢ − 1)⁺ ≤ 1`, which is equivalent for `θ > 0`. `ε > 0` is the standing
assumption of Definition 2.2; no smallness of `ε` is assumed, as on the page. -/
theorem lemma_2_1 {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m)
    (ϱ θ ε : ℝ) (hϱ : 0 < ϱ) (hθ : 0 < θ)
    (h215 : ∀ i, θ * max (D.theta i / D.mu i - 1) 0 ≤ 1) (hε : 0 < ε)
    (c : EReal) (hc : 1 ≤ c) :
    (∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), ∑ i, x i ≤ 0 →
      ⟪gradient (lyapV D ε θ) x, WithLp.toLp 2 (driftTrunc D ϱ c (WithLp.ofLp x) u)⟫ ≤
        ε * (θ * ϱ + m / (2 * ε) * (1 + ε * θ) - min θ 1 * l1 x) * lyapV D ε θ x) ∧
    ∀ x : EthierKurtz.SDEState m, 0 ≤ ∑ i, x i → ∀ u ∈ stdSimplex ℝ (Fin m),
      ⟪gradient (lyapV D ε θ) x, WithLp.toLp 2 (driftTrunc D ϱ c (WithLp.ofLp x) u)⟫ ≤
        -ε * (ϱ / m - θ * ϱ - θ * m / 2 + θ * negL1 x) * lyapV D ε θ x := by sorry

end UnifErgHW.Diffusion
