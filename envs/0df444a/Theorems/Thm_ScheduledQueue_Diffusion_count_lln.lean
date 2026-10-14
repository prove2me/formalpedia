-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_count_lln
-- name    : ScheduledQueue.Diffusion.count_lln
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:03.695234+00:00
-- url     : https://prove2.me/theorems/ce0898ae-c2b3-4651-aa9b-8915ed6049f6
-- title:
--   Proof of Corollary 1, p. 5 — N(ts)/t → s/h a.s.
-- statement:
--   Under the standing assumptions (i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, $U$ uniform on $[0,1]$ independent of $\xi$, $h>0$), for every $s\ge 0$, almost surely
--   $$
--   \frac{N(ts)}{t}\longrightarrow\frac{s}{h}\qquad (t\to\infty).
--   $$
--
--   This strong law for the counting process is used to replace the random time $N(st)$ by $st/h$ in the time change of the proof of Corollary 1.
--
--   **Formalization Note** The page writes "as $n\to\infty$"; the limit is in the real variable $t$. The null event may depend on $s$.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 5, proof of Corollary 1, first sentence

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem count_lln {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ s : ℝ, 0 ≤ s → ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ => (ScheduledQueue.Stability.count h ξ U (t * s) ω : ℝ) / t) atTop (𝓝 (s / h)) := by sorry

end ScheduledQueue.Diffusion
