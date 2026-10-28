-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_theorem_1
-- name    : ScheduledQueue.Stability.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:16.486857+00:00
-- url     : https://prove2.me/theorems/2f77c49c-4777-4a80-9dec-11e62cf1b1a0
-- title:
--   Theorem 1 — the critically loaded S/D/1 workload converges in distribution to a finite limit iff ξ₀⁺ is bounded
-- statement:
--   Let $h>0$, let $(\xi_j)_{j\in\mathbb Z}$ be i.i.d. perturbations with $\mathbb E|\xi_0|<\infty$, and let $U$ be uniform on $[0,1]$ and independent of $(\xi_j)$. Customers arrive at the times $jh+hU+\xi_j$ to a single unit-rate server; every customer brings exactly $h$ units of work ($V_1=h$, the critically loaded S/D/1 queue), and the system is empty at time $0$. Let $W(t)$ be the workload at time $t\ge0$.
--
--   Then there exists a finite-valued random variable $W(\infty)$ with
--   $$W(t)\Rightarrow W(\infty)\qquad(t\to\infty)$$
--   if and only if $\xi_0^+$ is a bounded random variable, i.e. $\xi_0\le c$ almost surely for some constant $c$.
--
--   Under critical loading a queue fed by renewal traffic is unstable; this theorem shows that scheduled traffic behaves differently, and that only the right tail of the perturbations (late arrivals) decides stability.
--
--   **Formalization Note.** "$\Rightarrow$" is Mathlib's `TendstoInDistribution` as $t\to\infty$ through the reals, and the finite-valued limit $W(\infty)$ is represented by its law $\nu$, a probability measure on $\mathbb R$ (the limit random variable is the identity on $(\mathbb R,\nu)$). A probability measure on $\mathbb R$ puts no mass at $+\infty$, so "$W(t)\Rightarrow\infty$" is not convergence in this sense. `TendstoInDistribution` includes almost-everywhere measurability of every $W(t)$, so in the "if" direction measurability is part of the conclusion, not an assumption. "$V_1=h$ a.s." and "$W(0)=0$" are built into the definition of the workload (see the setting, which also records the corrected workload formula).
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 5, Theorem 1

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledInput P ξ U) :
    (∃ ν : ProbabilityMeasure ℝ,
        TendstoInDistribution (fun t : ℝ => workload h ξ U t) atTop id (fun _ => P)
          (ν : Measure ℝ)) ↔
      ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c := by sorry

end ScheduledQueue.Stability
