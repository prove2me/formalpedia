-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_theorem_2_1_b
-- name    : UnifErgHW.Diffusion.theorem_2_1_b
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-21T19:44:00.4768+00:00
-- url     : https://prove2.me/theorems/717c394b-fdb8-49cf-abe3-8855a93f050f
-- title:
--   Theorem 2.1(b) and (2.29) from the drift condition (2.32): uniform exponential ergodicity of the Halfin–Whitt diffusion
-- statement:
--   This is the probabilistic half of Theorem 2.1 of Arapostathis–Hmedi–Pang: it shows that a uniform Foster–Lyapunov drift condition for the Halfin–Whitt limiting diffusion yields positive recurrence and uniform exponential ergodicity.
--
--   Consider the $m$-class limiting diffusion $\mathrm dX_t=b(X_t,v(X_t))\,\mathrm dt+\sigma\,\mathrm dW_t$ with centred drift $b(x,u)=-\frac{\varrho}{m}Me-M(x-\langle e,x\rangle^+u)-\langle e,x\rangle^+\Gamma u$, constant $\sigma=\mathrm{diag}(r_i)$, and stationary Markov control $v\in\mathfrak U_{\mathrm{sm}}$. Let $V=\exp(\Psi^*_{\varepsilon,\theta})$ be the function (2.16), with $\varepsilon,\theta>0$, and let $\mathcal L_u$ be the generator (2.7). Assume $\varrho>0$ and that for some $\kappa_0,\kappa_1>0$
--   $$\mathcal L_uV(x)\le\kappa_0-\kappa_1V(x)\qquad\forall\,(x,u)\in\mathbb R^m\times\Delta .\tag{2.32}$$
--   Then there are constants $\gamma,C>0$ such that for every $v\in\mathfrak U_{\mathrm{sm}}$ with transition function $P^v_t(x,\mathrm dy)$:
--
--   1. there is an invariant probability measure $\pi_v$ of $P^v$ with
--   $$\int_{\mathbb R^m}V\,\mathrm d\pi_v\le\frac{\kappa_0}{\kappa_1};$$
--   2. for all $t\ge0$ and $x\in\mathbb R^m$,
--   $$\bigl\|P^v_t(x,\cdot)-\pi_v\bigr\|_V\le C\,V(x)\,e^{-\gamma t}.$$
--
--   Combined with the Foster–Lyapunov equation (2.28), where $\kappa_1=\varepsilon\varrho/(2m)$, this gives (2.29) and (2.30), i.e. Theorem 2.1.
--
--   **Formalization Note** $P$ is any transition function of the strong SDE under $v$ (`IsMarkovTransition`: every measurable strong solution has law $P_t(x,\cdot)$; `strong_solution` shows one exists). An invariant measure is a probability measure $\pi$ with $\int P_t(x,\cdot)\,\pi(\mathrm dx)=\pi$ for all $t$. The $V$-norm is `tvNormWeighted` with weight $1+V$, which is infinite unless both measures integrate $1+V$. The integral of $V$ is a lower Lebesgue integral. The constants $\gamma,C$ are chosen before the control.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, pp. 10–11, proof of Theorem 2.1: (2.29) and part (b) (2.30), derived from (2.32) via (2.34) and [MeynT-94b, Theorem 2.3]

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

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, pp. 10–11, proof of Theorem 2.1: from the uniform drift condition (2.32) `L_uV ≤ κ₀ − κ₁V` on `ℝ^m × ∆` one obtains, under every `v ∈ 𝔘sm`, an invariant probability measure `π_v` with `∫V dπ_v ≤ κ₀/κ₁` ((2.29), via Itô's formula "in the usual manner") and the uniform `V`-norm exponential ergodicity (2.30) with constants `γ, C` independent of `v` (part (b)).

Formalization Note. Conventions as in `theorem_2_1`: `P` is any transition function of (2.1) under `v` (`IsMarkovTransition`; `strong_solution` shows one exists), "positive recurrent" is the existence of an invariant probability measure, and the `V`-norm is `tvNormWeighted` with weight `1 + V`. With `κ₁ = εϱ/(2m)` the integral bound is (2.29). -/
theorem theorem_2_1_b {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m)
    (ϱ ε θ : ℝ) (hℓ : IsCentered D ϱ) (hϱ : 0 < ϱ) (hε : 0 < ε) (hθ : 0 < θ)
    (κ₀ κ₁ : ℝ) (hκ₀ : 0 < κ₀) (hκ₁ : 0 < κ₁)
    (h232 : ∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), u ∈ stdSimplex ℝ (Fin m) →
      generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x ≤ κ₀ - κ₁ * lyapV D ε θ x) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ v : EthierKurtz.SDEState m → Fin m → ℝ, IsMarkovControl v →
        ∀ P : ℝ≥0 → EthierKurtz.SDEState m → Measure (EthierKurtz.SDEState m),
          IsMarkovTransition D v P →
          ∃ π : Measure (EthierKurtz.SDEState m), IsInvariantMeasure P π ∧
            ∫⁻ y, ENNReal.ofReal (lyapV D ε θ y) ∂π ≤ ENNReal.ofReal (κ₀ / κ₁) ∧
            ∀ (t : ℝ≥0) (x : EthierKurtz.SDEState m),
              tvNormWeighted (lyapV D ε θ) (P t x) π
                ≤ ENNReal.ofReal (C * lyapV D ε θ x * Real.exp (-γ * t)) := by sorry

end UnifErgHW.Diffusion
