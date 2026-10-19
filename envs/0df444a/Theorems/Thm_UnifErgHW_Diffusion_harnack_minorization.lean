-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_harnack_minorization
-- name    : UnifErgHW.Diffusion.harnack_minorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:27.150649+00:00
-- url     : https://prove2.me/theorems/72a58186-cc14-45e4-8ddd-4731c3c20781
-- title:
--   p. 11 — Harnack minorization P^v_1(x, 𝓑) ≥ δ_0 for x ∈ 𝓑, uniformly over v ∈ 𝔘sm
-- statement:
--   Assume the centred drift with $\varrho>0$ and the Foster–Lyapunov bound (2.32) for $V=\exp(\Psi^*_{\varepsilon,\theta})$, with $\varepsilon,\theta,\kappa_0,\kappa_1>0$. Then there is a radius $R>0$ and $\delta_0>0$ such that, writing $\mathcal B_R$ for the closed Euclidean ball of radius $R$ about the origin, $\kappa_0/\kappa_1\le e^{-\kappa_1/2}(1-e^{-\kappa_1/2})V(x)$ outside $\mathcal B_R$ and
--   $$
--   P^v_1(x,\mathcal B_R)\ge\delta_0\qquad\forall\,x\in\mathcal B_R,\ \forall\,v\in\mathfrak U_{\mathrm{sm}},
--   $$
--   for every transition function $P^v$ of the SDE (2.1) under $v$.
--
--   This is the uniform minorization condition on a ball which, together with the moment bound (2.34), gives the geometric ergodicity bound (2.35) with constants that do not depend on the control. The paper derives it from the parabolic Harnack inequality for nondivergence-form operators.
--
--   **Formalization Note** The ball is the one selected from $\kappa_0,\kappa_1$ after (2.34). Its radius and $\delta_0$ may depend on the model and drift constants, but not on $v$.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 11, proof of Theorem 2.1(b) (parabolic Harnack inequality, [22, Theorem 4.1])

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

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 11 (proof of Theorem 2.1(b), via the parabolic Harnack inequality [22, Theorem 4.1]):
one can choose the ball `𝓑` required after (2.34) and a `δ₀ > 0` such that
`P^v_1(x, 𝓑) ≥ δ₀` for all `x ∈ 𝓑` and all `v ∈ 𝔘sm`.

Formalization Note. The ball is a closed Euclidean ball centred at the origin. Its radius is
constructed after the drift condition (2.32), and its complement satisfies the displayed
inequality immediately following (2.34). The lower bound is uniform in the control and the
transition function. -/
theorem harnack_minorization {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m)
    (ϱ ε θ : ℝ) (hℓ : IsCentered D ϱ) (hϱ : 0 < ϱ)
    (hε : 0 < ε) (hθ : 0 < θ) (κ₀ κ₁ : ℝ) (hκ₀ : 0 < κ₀) (hκ₁ : 0 < κ₁)
    (h232 : ∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), u ∈ stdSimplex ℝ (Fin m) →
      generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x ≤ κ₀ - κ₁ * lyapV D ε θ x) :
    ∃ R : ℝ, 0 < R ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      (∀ x : EthierKurtz.SDEState m, x ∉ Metric.closedBall (0 : EthierKurtz.SDEState m) R →
        κ₀ / κ₁ ≤ Real.exp (-κ₁ / 2) * (1 - Real.exp (-κ₁ / 2)) * lyapV D ε θ x) ∧
      ∀ v : EthierKurtz.SDEState m → Fin m → ℝ, IsMarkovControl v →
        ∀ P : ℝ≥0 → EthierKurtz.SDEState m → Measure (EthierKurtz.SDEState m),
          IsMarkovTransition D v P →
          ∀ x ∈ Metric.closedBall (0 : EthierKurtz.SDEState m) R,
            ENNReal.ofReal δ₀ ≤ P 1 x (Metric.closedBall 0 R) := by sorry

end UnifErgHW.Diffusion
