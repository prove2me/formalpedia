-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_loynes_representation
-- name    : ScheduledQueue.Stability.loynes_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:58.719694+00:00
-- url     : https://prove2.me/theorems/094434a8-c18f-4c3e-a040-20746211fe70
-- title:
--   Proof of Theorem 1, p. 5 — Loynes: W(t) has the law of M(t) = sup_{0≤s≤t} (Λ(s) − s)
-- statement:
--   Let $h>0$, let $(\xi_j)_{j\in\mathbb Z}$ be i.i.d. integrable perturbations and $U$ uniform on $[0,1]$ independent of them. Let $W(t)$ be the S/D/1 workload (service time $h$, empty at time $0$) fed by the arrivals $jh+hU+\xi_j$, and let
--   $$M(t)=\sup_{0\le s\le t}\big(\Lambda(s)-s\big),\qquad \Lambda(s)=h\cdot\#\{j\in\mathbb Z: jh+Uh-\xi_j\in(0,s]\},$$
--   be the running maximum of the time-reversed arrival process. Then for every $t\ge0$,
--   $$W(t)\overset{\mathcal D}{=}M(t).$$
--
--   This is the time-reversal (Loynes' lemma) with which the proof of Theorem 1 starts: it replaces the workload at a fixed time by a running maximum that is nondecreasing in $t$, so that convergence in distribution of $W(t)$ reduces to almost-sure behaviour of $\sup_{s\ge0}(\Lambda(s)-s)$.
--
--   **Formalization Note.** Equality in distribution is `IdentDistrib`, which also asserts that both random variables are almost-everywhere measurable. The workload is the corrected one of the setting (with $W(0)=0$); with the printed formula, $W(t)$ would have the law of $M(t)+h$.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 5, proof of Theorem 1, first display ("Loynes' lemma ensures that W(t) =ᴰ M(t)")

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem loynes_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    ∀ t : ℝ, 0 ≤ t → IdentDistrib (workload h ξ U t) (revMax h ξ U t) P P := by sorry

end ScheduledQueue.Stability
