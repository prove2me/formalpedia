-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_op_reduction
-- name    : ScheduledQueue.Diffusion.op_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:03.971+00:00
-- url     : https://prove2.me/theorems/260c079f-cd2a-4818-809f-74832398b1cc
-- title:
--   Proof of Corollary 1, p. 5 — t^{-1/2} max_{s≤t} Σ_{i≤N(s)} V_i − s = t^{-1/2} max_{s≤1} Σ_{i≤N(st)} (V_i − EV_i) + o_p(1)
-- statement:
--   Under the standing assumptions (i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), let $V_1,V_2,\dots$ be i.i.d. service times with finite variance, independent of $(U,\xi)$, with $\mathbb EV_1=h$ (critical loading). Then, as $t\to\infty$,
--   $$
--   t^{-1/2}\max_{0\le s\le t}\Big(\sum_{i=1}^{N(s)}V_i-s\Big)
--   = t^{-1/2}\max_{0\le s\le 1}\sum_{i=1}^{N(st)}\big(V_i-\mathbb EV_i\big)+o_p(1),
--   $$
--   that is, the difference of the two sides tends to $0$ in probability.
--
--   The reduction removes the arrival process from the diffusion-scale workload, up to the time change $s\mapsto N(st)$: by Proposition 1, $hN(s)-s$ is only $o_p(\log t)$ uniformly over $[0,t]$.
--
--   **Formalization Note** Convergence in probability is `TendstoInMeasure`. $\mathbb EV_i=h$ for all $i$, so the centered summands are written $V_i-h$. The maxima are real suprema; off a null event they are suprema of bounded families. $t^{-1/2}$ for $t\le 0$ is a junk value, irrelevant to the limit.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 5, proof of Corollary 1, display (first line)

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem op_reduction {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U)
    (V : ℕ → Ω → ℝ) (hV : ServiceInput P ξ U V) (hmean : ∫ ω, V 1 ω ∂P = h) :
    TendstoInMeasure P
      (fun (t : ℝ) ω =>
        (Real.sqrt t)⁻¹ * (⨆ s : Icc 0 t, ((∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ U s ω), V i ω) - s))
          - (Real.sqrt t)⁻¹ *
            ⨆ s : Icc (0 : ℝ) 1, ∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h ξ U (s * t) ω), (V i ω - h))
      atTop (fun _ => 0) := by sorry

end ScheduledQueue.Diffusion
