-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_necessity
-- name    : ScheduledQueue.Stability.necessity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:16.73489+00:00
-- url     : https://prove2.me/theorems/3814882c-3ea0-438c-bd1f-6a8295922bb2
-- title:
--   Proof of Theorem 1, p. 7 — if ξ₀⁺ is unbounded, then sup_{s≥0} (Λ(s) − s) = ∞ a.s.
-- statement:
--   In the scheduled-traffic model with $h>0$, i.i.d. integrable perturbations $(\xi_j)_{j\in\mathbb Z}$ and an independent uniform shift $U$, suppose that $\xi_0^+$ is not a bounded random variable. Then almost surely
--   $$\sup_{s\ge0}\big(\Lambda(s)-s\big)=\infty,\qquad \Lambda(s)=h\cdot\#\{j\in\mathbb Z: jh+Uh-\xi_j\in(0,s]\}.$$
--
--   Since the workload $W(t)$ has the law of $M(t)=\sup_{0\le s\le t}(\Lambda(s)-s)$, this gives $W(t)\Rightarrow\infty$, the "only if" direction of Theorem 1.
--
--   **Formalization Note.** "$=\infty$" is stated as: for almost every outcome and every real $C$ there is $s\ge0$ with $\Lambda(s)-s>C$. $\Lambda$ converts the count with `ENat.toNat`, whose value at an infinite count is $0$; this junk value can only make the statement harder to satisfy.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 7, proof of Theorem 1, "we may conclude that max_{s≥0} Λ(s) − s = ∞ a.s."

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem necessity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (¬ ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) →
      ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ s : ℝ, 0 ≤ s ∧ C < Lam h ξ U s ω - s := by sorry

end ScheduledQueue.Stability
