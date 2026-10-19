-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_strong_solution
-- name    : UnifErgHW.Diffusion.strong_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:58.446558+00:00
-- url     : https://prove2.me/theorems/8505cbb7-217a-4244-9701-cedddf0522b5
-- title:
--   p. 5 — under every stationary Markov control the SDE (2.1) has a unique strong solution and a strong Feller transition function
-- statement:
--   Let $v:\mathbb R^m\to\Delta$ be a Borel measurable stationary Markov control, and consider the SDE
--   $$
--   \mathrm dX_t=b\big(X_t,v(X_t)\big)\,\mathrm dt+\sigma\,\mathrm dW_t ,\qquad X_0=x,
--   $$
--   with $b(x,u)=\ell-M(x-\langle e,x\rangle^+u)-\langle e,x\rangle^+\Gamma u$ and the constant diagonal matrix $\sigma=\mathrm{diag}(r_1,\dots,r_m)$, $r_i>0$. Then:
--
--   1. for every initial point $x\in\mathbb R^m$ there is a strong solution: a continuous solution adapted to the Brownian motion's completed natural filtration;
--   2. any two strong solutions started at $x$ and driven by the same Brownian motion agree almost surely at every time;
--   3. there is a transition function $P^v_t(x,\mathrm dy)$: on every probability space with a standard Brownian motion, every measurable strong solution started at $x$ has law $P^v_t(x,\cdot)$ at time $t$; for $t>0$ it maps bounded Borel functions to continuous functions of $x$.
--
--   The paper cites this as well known (unique strong solution, Gyöngy–Krylov). It is what makes $P^v_t$ in Theorem 2.1 well defined, and it shows that the transition-function hypothesis of the later statements is not vacuous.
--
--   **Formalization Note** Adaptedness is expressed by measurable dependence on the Brownian path stopped at each time. The drift is only Borel in $x$ (the control $v$ need not be continuous). The transition predicate ranges over measurable strong solutions, as in the paper; the published `IsTransitionFunction` additionally ranges over nonmeasurable pathwise solutions.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 5, §2.1 (definition of 𝔘sm and P^v_t, citing [24])

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

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 5 (§2.1, citing [24]): under every stationary Markov control `v ∈ 𝔘sm` the SDE (2.1)
has a unique strong solution which is a strong Feller process with transition function `P^v_t(x, dy)`.

Formalization Note. `IsStrongSolution` includes the pathwise SDE and adaptedness to the completed
natural filtration of `B`, expressed by measurable dependence on the stopped Brownian path at each
time. Uniqueness is equality almost surely at each time for two strong solutions driven by the same
Brownian motion. `IsStrongFeller` maps bounded Borel functions to continuous functions at positive
times. The transition-function clause also records uniqueness in law for measurable strong solutions. -/
theorem strong_solution {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m)
    (v : EthierKurtz.SDEState m → Fin m → ℝ) (hv : IsMarkovControl v) :
    (∀ x : EthierKurtz.SDEState m, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pr : Measure Ω)
        (B X : ℝ≥0 → Ω → EthierKurtz.SDEState m),
        IsProbabilityMeasure Pr ∧ EthierKurtz.IsStandardBrownian Pr B ∧
          IsStrongSolution Pr (markovDrift D v) (sigma D) B X x) ∧
      ∃ P : ℝ≥0 → EthierKurtz.SDEState m → Measure (EthierKurtz.SDEState m),
        IsMarkovTransition D v P ∧ IsStrongFeller P ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
            (B X Y : ℝ≥0 → Ω → EthierKurtz.SDEState m) (x : EthierKurtz.SDEState m),
            EthierKurtz.IsStandardBrownian Pr B →
            IsStrongSolution Pr (markovDrift D v) (sigma D) B X x →
            IsStrongSolution Pr (markovDrift D v) (sigma D) B Y x →
            ∀ t : ℝ≥0, ∀ᵐ ω ∂Pr, X t ω = Y t ω := by sorry

end UnifErgHW.Diffusion
