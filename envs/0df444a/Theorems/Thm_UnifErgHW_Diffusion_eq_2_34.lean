-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_eq_2_34
-- name    : UnifErgHW.Diffusion.eq_2_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:51.867225+00:00
-- url     : https://prove2.me/theorems/7e4203d7-28a4-40f6-9f53-55a69ff5b6e1
-- title:
--   (2.34), p. 11 — ∫P^v_t(x,dy)V(y) ≤ κ_0/κ_1 + e^{−κ_1 t}V(x) under L_uV ≤ κ_0 − κ_1V, for every v ∈ 𝔘sm
-- statement:
--   Let $V=\exp(\Psi^*_{\varepsilon,\theta})$ be the Lyapunov function of (2.16), with $\varepsilon,\theta>0$, and suppose that, for constants $\kappa_0,\kappa_1>0$,
--   $$
--   \mathcal L_uV(x)\le\kappa_0-\kappa_1V(x)\qquad\forall\,(x,u)\in\mathbb R^m\times\Delta. \tag{2.32}
--   $$
--   Then for every stationary Markov control $v\in\mathfrak U_{\mathrm{sm}}$, every transition function $P^v$ of the SDE (2.1) under $v$, every $t\ge0$ and every $x\in\mathbb R^m$,
--   $$
--   \int_{\mathbb R^m}P^v_t(x,\mathrm dy)\,V(y)\le\frac{\kappa_0}{\kappa_1}+e^{-\kappa_1t}V(x).
--   $$
--
--   This uniform moment bound, with the minorization on a ball, yields geometric ergodicity of the skeleton chain.
--
--   **Formalization Note** The integral is the lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 11, (2.32) and (2.34), citing [4, Lemma 2.5.5]

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

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 11, (2.34) (citing [4, Lemma 2.5.5]): if the function `V` of (2.16) satisfies
the drift condition (2.32) `L_uV(x) ≤ κ₀ − κ₁V(x)` for all `(x, u) ∈ ℝ^m × ∆`, with `κ₀, κ₁ > 0`, then
`∫P^v_t(x, dy)V(y) = E^v_x[V(X_t)] ≤ κ₀/κ₁ + e^{−κ₁t}V(x)` for all `t ≥ 0`, `x ∈ ℝ^m` and
`v ∈ 𝔘sm`.

Formalization Note. The integral is a lower Lebesgue integral in `[0, ∞]`, so it is never a junk
value. `P` is any transition function of (2.1) under `v` (`IsMarkovTransition`);
`strong_solution` shows one exists. -/
theorem eq_2_34 {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m)
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (κ₀ κ₁ : ℝ) (hκ₀ : 0 < κ₀) (hκ₁ : 0 < κ₁)
    (h232 : ∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), u ∈ stdSimplex ℝ (Fin m) →
      generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x ≤ κ₀ - κ₁ * lyapV D ε θ x) :
    ∀ v : EthierKurtz.SDEState m → Fin m → ℝ, IsMarkovControl v →
      ∀ P : ℝ≥0 → EthierKurtz.SDEState m → Measure (EthierKurtz.SDEState m),
        IsMarkovTransition D v P →
        ∀ (t : ℝ≥0) (x : EthierKurtz.SDEState m),
          ∫⁻ y, ENNReal.ofReal (lyapV D ε θ y) ∂(P t x) ≤
            ENNReal.ofReal (κ₀ / κ₁ + Real.exp (-κ₁ * t) * lyapV D ε θ x) := by sorry

end UnifErgHW.Diffusion
