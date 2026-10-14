-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_late_exp_moment
-- name    : ScheduledQueue.Diffusion.late_exp_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:05.93175+00:00
-- url     : https://prove2.me/theorems/1506c48c-7541-4e00-ae0a-5841d27b6013
-- title:
--   Proof of Proposition 1, p. 4 — E exp(θ𝓛(0)) ≤ exp((e^θ − 1)(Eξ⁺/h + 1))
-- statement:
--   Under the standing assumptions (i.i.d. perturbations $\xi_j$ with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), let $\mathcal L(0)=\#\{i : ih+Uh<0,\ ih+Uh+\xi_i\ge 0\}$ be the number of customers scheduled before time $0$ who arrive at or after time $0$, and $\xi_0^+=\max(\xi_0,0)$. Then $\mathcal L(0)<\infty$ almost surely and, for every $\theta>0$,
--   $$
--   \mathbb E\exp\big(\theta\,\mathcal L(0)\big)\le \exp\Big((e^\theta-1)\Big(\frac{\mathbb E\xi_0^+}{h}+1\Big)\Big)<\infty .
--   $$
--
--   This is the late-customer counterpart of the bound on $\mathcal E(0)$ and plays the same role in the proof of Proposition 1.
--
--   **Formalization Note** As for $\mathcal E(0)$: $\mathcal L(0)$ is an extended natural number, its almost sure finiteness is part of the statement, and the expectation is a lower Lebesgue integral; $\mathbb E\xi_0^+$ is a Bochner integral of an integrable function.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 4, proof of Proposition 1, first display

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem late_exp_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ θ : ℝ, 0 < θ →
      (∀ᵐ ω ∂P, late h ξ U 0 ω ≠ ⊤) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((late h ξ U 0 ω).toNat : ℝ))) ∂P ≤
        ENNReal.ofReal (Real.exp ((Real.exp θ - 1) * ((∫ ω, max (ξ 0 ω) 0 ∂P) / h + 1))) := by sorry

end ScheduledQueue.Diffusion
