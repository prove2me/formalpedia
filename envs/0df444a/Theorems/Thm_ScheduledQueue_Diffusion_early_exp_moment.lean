-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_early_exp_moment
-- name    : ScheduledQueue.Diffusion.early_exp_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:01.569038+00:00
-- url     : https://prove2.me/theorems/05579093-56a9-4700-a340-54fc86867886
-- title:
--   Proof of Proposition 1, p. 3 — E exp(θ𝓔(0)) ≤ exp((e^θ − 1)(Eξ⁻/h + 1))
-- statement:
--   Under the standing assumptions (i.i.d. perturbations $\xi_j$ with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), let $\mathcal E(0)=\#\{i : ih+Uh>0,\ ih+Uh+\xi_i\le 0\}$ be the number of customers scheduled after time $0$ who arrive by time $0$, and $\xi_0^-=\max(-\xi_0,0)$. Then $\mathcal E(0)<\infty$ almost surely and, for every $\theta>0$,
--   $$
--   \mathbb E\exp\big(\theta\,\mathcal E(0)\big)\le \exp\Big((e^\theta-1)\Big(\frac{\mathbb E\xi_0^-}{h}+1\Big)\Big)<\infty .
--   $$
--
--   Together with its counterpart for $\mathcal L(0)$, this exponential moment bound is what makes the maximum of $n$ stationary copies of $\mathcal E$ of order $o(\log n)$ in probability in the proof of Proposition 1.
--
--   **Formalization Note** $\mathcal E(0)$ is an extended natural number; the statement asserts that it is almost surely finite and bounds the expectation of $\exp(\theta\,\mathcal E(0))$ as a lower Lebesgue integral of a nonnegative function (Lean's `toNat` sends $\infty$ to $0$, which affects only the null event where $\mathcal E(0)=\infty$). $\mathbb E\xi_0^-$ is the Bochner integral of the integrable function $\max(-\xi_0,0)$. The printed chain of displays contains two misprints (a sign in "$-jh+uh$" and a spurious "log"); its final bound, stated here, is correct.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 3, proof of Proposition 1, display bounding E exp(θ𝓔(0))

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem early_exp_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ θ : ℝ, 0 < θ →
      (∀ᵐ ω ∂P, early h ξ U 0 ω ≠ ⊤) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((early h ξ U 0 ω).toNat : ℝ))) ∂P ≤
        ENNReal.ofReal (Real.exp ((Real.exp θ - 1) * ((∫ ω, max (-ξ 0 ω) 0 ∂P) / h + 1))) := by sorry

end ScheduledQueue.Diffusion
