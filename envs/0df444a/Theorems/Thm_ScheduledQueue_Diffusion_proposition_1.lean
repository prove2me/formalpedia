-- Prove2me | Theorems.Thm_ScheduledQueue_Diffusion_proposition_1
-- name    : ScheduledQueue.Diffusion.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:10.782605+00:00
-- url     : https://prove2.me/theorems/7b7498f2-d17a-46b8-9d71-60f8446b3428
-- title:
--   Proposition 1 — (1/log n) max_{0≤s≤1} |h N(ns) − ns| ⇒ 0
-- statement:
--   Let the perturbations $(\xi_j)_{j\in\mathbb Z}$ be i.i.d. with $\mathbb E|\xi_0|<\infty$, let $U$ be uniform on $[0,1]$ and independent of $\xi$, let $h>0$, and let $N(t)$ be the number of arrivals $jh+hU+\xi_j$ in $(0,t]$. Then, as $n\to\infty$ through the integers,
--   $$
--   \frac{1}{\log n}\max_{0\le s\le 1}\big|h\,N(ns)-ns\big|\;\Rightarrow\;0 .
--   $$
--
--   Scheduled traffic thus deviates from its fluid approximation $s\mapsto s/h$ by only $o(\log n)$ uniformly over $[0,n]$, far less than the $\sqrt n$ fluctuations of a renewal process. This is what makes the arrival variability invisible on the diffusion scale in Corollary 1.
--
--   **Formalization Note** Convergence in distribution to the constant $0$ is equivalent to convergence in probability, and the statement is written as convergence in probability (`TendstoInMeasure`). The maximum is a real supremum over $s\in[0,1]$; off a null event the counts are finite and the family is bounded by $hN(n)+n$. For $n\le 1$, $1/\log n$ is a junk value, irrelevant to the limit.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 3, Proposition 1

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

namespace ScheduledQueue.Diffusion

open MeasureTheory ProbabilityTheory Set Filter Topology NNReal

theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (Real.log n)⁻¹ *
        ⨆ s : Icc (0 : ℝ) 1, |h * (ScheduledQueue.Stability.count h ξ U ((n : ℝ) * s) ω : ℝ) - (n : ℝ) * s|)
      atTop (fun _ => 0) := by sorry

end ScheduledQueue.Diffusion
