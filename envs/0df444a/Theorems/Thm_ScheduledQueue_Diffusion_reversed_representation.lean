-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_reversed_representation
-- name    : ScheduledQueue.Diffusion.reversed_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:56.386157+00:00
-- url     : https://prove2.me/theorems/7cea7ef9-9df7-4d6c-acb7-d14dbe2556a1
-- title:
--   Proof of Corollary 1, p. 4 — reversed-time representation W(t) =D max_{0≤s≤t} Σ_{i≤N̂(s)} V_i − s (implicit step)
-- statement:
--   Under the standing assumptions (i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$, i.i.d. service times $V_1,V_2,\dots$ with finite variance, independent of $(U,\xi)$), let $\hat N(s)$ be the number of points $jh+hU-\xi_j$ in $(0,s]$: the counting function of the time-reversed arrival process, whose perturbations are $-\xi_j$. Then for every $t\ge 0$,
--   $$
--   W(t)\overset{D}{=}\max_{0\le s\le t}\Big(\sum_{i=1}^{\hat N(s)}V_i-s\Big).
--   $$
--
--   Looking backwards from time $t$, the work that arrived in the last $s$ time units is the sum of the service times of the reversed arrivals in $(0,s]$; stationarity of the input turns this pathwise identity into an equality in law. The proof of Corollary 1 starts from the right-hand side.
--
--   **Formalization Note** The page uses this representation without stating it, and writes $N(s)$ on the right-hand side. That $N$ is the count of the time-reversed process, with perturbations $-\xi_j$; with the forward count the equality in law fails unless $\xi_0$ is symmetric. Every other statement of this mission holds for any perturbation sequence satisfying the standing assumptions, hence also for $-\xi$. Equality in distribution includes almost-everywhere measurability of both sides.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 4, proof of Corollary 1, first display (implicit step)

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem reversed_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U)
    (V : ℕ → Ω → ℝ) (hV : ServiceInput P ξ U V) :
    ∀ t : ℝ, 0 ≤ t →
      IdentDistrib (workload h ξ U V t)
        (fun ω => ⨆ s : Icc 0 t,
          ((∑ i ∈ Finset.Icc 1 (ScheduledQueue.Stability.count h (fun j ω' => -ξ j ω') U s ω), V i ω) - s)) P P := by sorry

end ScheduledQueue.Diffusion
