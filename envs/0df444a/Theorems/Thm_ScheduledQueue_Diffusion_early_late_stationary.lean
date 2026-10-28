-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_early_late_stationary
-- name    : ScheduledQueue.Diffusion.early_late_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:06.214986+00:00
-- url     : https://prove2.me/theorems/17388786-853e-4277-9cbb-93a9d2f8f299
-- title:
--   Proof of Proposition 1, p. 3 — 𝓔(t) and 𝓛(t) are time-stationary
-- statement:
--   Under the standing assumptions (i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), the processes of early and late customers are time-stationary: for every real $t$,
--   $$
--   \big(\mathcal E(t+s)\big)_{s\in\mathbb R}\overset{D}{=}\big(\mathcal E(s)\big)_{s\in\mathbb R},\qquad \big(\mathcal L(t+s)\big)_{s\in\mathbb R}\overset{D}{=}\big(\mathcal L(s)\big)_{s\in\mathbb R},
--   $$
--   where $\mathcal E(t)=\#\{i : ih+Uh>t,\ ih+Uh+\xi_i\le t\}$ and $\mathcal L(t)=\#\{i : ih+Uh<t,\ ih+Uh+\xi_i\ge t\}$, as random variables with values in $\{0,1,\dots\}\cup\{\infty\}$.
--
--   This is how the proof of Proposition 1 replaces $\mathbb P(\mathcal E(kh)>\varepsilon\log n)$ by $\mathbb P(\mathcal E(0)>\varepsilon\log n)$.
--
--   **Formalization Note** Equality in distribution of the processes is equality of their laws on $\{0,1,\dots,\infty\}^{\mathbb R}$ with the product $\sigma$-algebra, i.e. of all finite-dimensional distributions; it includes almost-everywhere measurability of both sides. Each process is stated stationary separately, as on the page.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 3, proof of Proposition 1, second sentence

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem early_late_stationary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ t : ℝ,
      IdentDistrib (fun ω (s : ℝ) => early h ξ U (t + s) ω) (fun ω (s : ℝ) => early h ξ U s ω) P P ∧
      IdentDistrib (fun ω (s : ℝ) => late h ξ U (t + s) ω) (fun ω (s : ℝ) => late h ξ U s ω) P P := by sorry

end ScheduledQueue.Diffusion
