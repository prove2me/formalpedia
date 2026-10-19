-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_theorem_2_1
-- name    : UnifErgHW.Diffusion.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:19.035891+00:00
-- url     : https://prove2.me/theorems/cfcaf257-b299-4ccd-8493-740daef56947
-- title:
--   Theorem 2.1, p. 10 — for ϱ > 0 the multiclass Halfin–Whitt diffusion is exponentially ergodic uniformly over all stationary Markov controls
-- statement:
--   Consider the limiting diffusion of an $m$-class many-server queue in the Halfin–Whitt regime,
--   $$
--   \mathrm dX_t=b(X_t,U_t)\,\mathrm dt+\sigma\,\mathrm dW_t,\qquad b(x,u)=-\frac{\varrho}{m}Me-M\big(x-\langle e,x\rangle^+u\big)-\langle e,x\rangle^+\Gamma u,
--   $$
--   with service rates $M=\mathrm{diag}(\mu_i)>0$, abandonment rates $\Gamma=\mathrm{diag}(\gamma_i)\ge0$, spare capacity $\varrho$, controls $u\in\Delta$, and $\sigma=\mathrm{diag}(r_i)$ with $\sum_i r_i^2/(2\mu_i)=1$. Let $\beta_i=\gamma_i/\mu_i$. Assume $\varrho>0$, $\theta(\beta_{\max}-1)^+\le1$ (2.15), and
--   $$
--   0<\theta\le\frac{\varrho}{3m(2\varrho+m)} .\tag{2.27}
--   $$
--   Let $V=\exp(\Psi^*_{\varepsilon,\theta})$ be the function (2.16). Then:
--
--   1. **(a)** There is $\varepsilon_0>0$ such that for each $0<\varepsilon\le\varepsilon_0$ there is $\kappa_0>0$ with
--   $$
--   \mathcal L_uV(x)\le\kappa_0-\varepsilon\Big(\frac{\varrho}{2m}+\frac{\theta}{2}\|x^-\|_1\Big)V(x)\qquad\forall\,(x,u)\in\mathbb R^m\times\Delta .
--   $$
--   Moreover, under every stationary Markov control $v\in\mathfrak U_{\mathrm{sm}}$ the process has an invariant probability measure $\pi_v$, and
--   $$
--   \int_{\mathbb R^m}V\,\mathrm d\pi_v\le\frac{2m}{\varepsilon\varrho}\,\kappa_0 .
--   $$
--   2. **(b)** There are constants $\gamma,C_\gamma>0$, not depending on the control, such that
--   $$
--   \big\|P^v_t(x,\cdot)-\pi_v\big\|_V\le C_\gamma\,V(x)\,e^{-\gamma t}\qquad\forall\,(t,x)\in\mathbb R_+\times\mathbb R^m,\ \forall\,v\in\mathfrak U_{\mathrm{sm}} .
--   $$
--
--   Positive spare capacity therefore makes the limiting diffusion exponentially ergodic at a rate that is uniform over all stationary Markov scheduling policies.
--
--   **Formalization Note**
--   1. The paper prints $\theta$ instead of $\theta/2$ in front of $\|x^-\|_1$ in (a); as printed it fails along $x=-Re$, $R\to\infty$. The rest of the theorem uses only $\mathcal L_uV\le\kappa_0-\frac{\varepsilon\varrho}{2m}V$ and is as printed.
--   2. The drift is centred (Remark 2.3), $\sigma$ is the constant matrix $\mathrm{diag}(r_i)$, and $\sum_i r_i^2/(2\mu_i)=1$ is the normalization $\sum_i\tilde\lambda_i/\mu_i=1$ used in the proof's (2.31). Condition (2.15) is written coordinatewise.
--   3. A control $v\in\mathfrak U_{\mathrm{sm}}$ is a Borel map into $\Delta$; under it the process solves (2.1) with drift $x\mapsto b(x,v(x))$, and $P^v$ is a transition function of measurable strong solutions of that SDE (one exists by the item for p. 5). "Positive recurrent" is formalized as the existence of an invariant probability measure.
--   4. The $V$-norm uses the weight $1+V$ (the paper's $f$-norm (1.1) needs $f\ge1$, and $V$ can be below $1$); it is infinite unless both measures integrate $1+V$.
--   5. The constants are chosen in the order $\varepsilon_0$, $\varepsilon$, $\kappa_0$, then $\gamma,C_\gamma$, all before the control.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 10, Theorem 2.1, (2.27)–(2.30)

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

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 10, Theorem 2.1: assume `ϱ > 0`, (2.15) and `0 < θ ≤ ϱ/(3m(2ϱ + m))` (2.27).
(a) There is `ε₀ > 0` such that for each `0 < ε ≤ ε₀` the function `V` of (2.16) satisfies the
Foster–Lyapunov equation `L_uV(x) ≤ κ₀ − ε(ϱ/(2m) + (θ/2)‖x⁻‖₁)V(x)` for all `(x, u) ∈ ℝ^m × ∆` and
some `κ₀ > 0`; under every `v ∈ 𝔘sm` the process has an invariant probability measure `π_v`, and
`∫V dπ_v ≤ (2m/(εϱ))κ₀` (2.29).
(b) There are `γ, C_γ > 0` such that `‖P^v_t(x,·) − π_v‖_V ≤ C_γV(x)e^{−γt}` for all `t ≥ 0`,
`x ∈ ℝ^m` and `v ∈ 𝔘sm` (2.30).

Formalization Note.
* (2.28) is posed with `θ/2` in place of the printed `θ` on `‖x⁻‖₁`; as printed it is false (see
  `eq_2_28`). (2.29) and (b) only use `L_uV ≤ κ₀ − (εϱ/(2m))V` and are as printed.
* The drift is centred, `ℓ = −(ϱ/m)Me` (Remark 2.3), `σ = diag(r)` is constant, and
  `∑ᵢrᵢ²/(2µᵢ) = 1` (`∑λ̃ᵢ/µᵢ = 1`, used in the proof's (2.31)). (2.15) is `∀ i, θ(βᵢ − 1)⁺ ≤ 1`.
* `v ∈ 𝔘sm` is `IsMarkovControl v` (Borel, `∆`-valued); the process under `v` solves (2.1) with drift
  `x ↦ b(x, v(x))`, and `P` is any transition function of it (all measurable strong solutions have law `P t x`;
  `strong_solution` shows one exists). "Positive recurrent" is read as the existence of an invariant
  probability measure `π` of `P`; `π` is the `π_v` of (2.29)–(2.30).
* The `V`-norm (1.1) is the published `tvNormWeighted` with weight `1 + V` (`V` itself is not
  `≥ 1`); it is `∞` unless both measures integrate `1 + V`.
* Order of constants: `ε₀`, then `ε`, then `κ₀`, then `γ, C`, all before the control `v`. -/
theorem theorem_2_1 {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m)
    (ϱ θ : ℝ) (hℓ : IsCentered D ϱ) (hϱ : 0 < ϱ) (hσ : IsNormalized D)
    (h215 : ∀ i, θ * max (D.theta i / D.mu i - 1) 0 ≤ 1)
    (hθ : 0 < θ) (h227 : θ ≤ ϱ / (3 * m * (2 * ϱ + m))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      (∀ (x : EthierKurtz.SDEState m) (u : Fin m → ℝ), u ∈ stdSimplex ℝ (Fin m) →
          generator (ctrlDrift D u) (sigma D) (lyapV D ε θ) x
            ≤ κ₀ - ε * (ϱ / (2 * m) + θ / 2 * negL1 x) * lyapV D ε θ x) ∧
      ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
        ∀ v : EthierKurtz.SDEState m → Fin m → ℝ, IsMarkovControl v →
          ∀ P : ℝ≥0 → EthierKurtz.SDEState m → Measure (EthierKurtz.SDEState m),
            IsMarkovTransition D v P →
            ∃ π : Measure (EthierKurtz.SDEState m), IsInvariantMeasure P π ∧
              ∫⁻ y, ENNReal.ofReal (lyapV D ε θ y) ∂π ≤
                ENNReal.ofReal (2 * m / (ε * ϱ) * κ₀) ∧
              ∀ (t : ℝ≥0) (x : EthierKurtz.SDEState m),
                tvNormWeighted (lyapV D ε θ) (P t x) π
                  ≤ ENNReal.ofReal (C * lyapV D ε θ x * Real.exp (-γ * t)) := by sorry

end UnifErgHW.Diffusion
