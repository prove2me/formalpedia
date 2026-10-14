-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_ergodic_recurrence
-- name    : ScheduledQueue.Stability.ergodic_recurrence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:16.925074+00:00
-- url     : https://prove2.me/theorems/f8a85fc2-081b-408e-bf89-4c0afa13e143
-- title:
--   Proof of Theorem 1, p. 6 — ergodic theorem: (1/n) Σ_{j≤n} I(Y_j ≤ l) → ℙ(Y₀ ≤ l) a.s.
-- statement:
--   In the scheduled-traffic model with $h>0$, i.i.d. integrable perturbations $(\xi_j)_{j\in\mathbb Z}$ and an independent uniform shift $U$, let $Y_n=\sum_{j\ge1}I(-\xi_{n+1-j}>(j-2)h)$. Then:
--
--   1. there is a finite level $l$ with $\mathbb P(Y_0\le l)>0$;
--   2. for every $l\in\{0,1,2,\dots\}$, almost surely
--   $$\frac1n\sum_{j=1}^n I(Y_j\le l)\;\longrightarrow\;\mathbb P(Y_0\le l)\qquad(n\to\infty).$$
--
--   Each $Y_n$ is the same function of the shifted i.i.d. sequence $(\xi_{n+j})_{j\in\mathbb Z}$, so this is the pointwise ergodic theorem for the shift. With $l$ as in part 1 the limit is positive, so $Y_n\le l$ for infinitely many $n$ almost surely: this produces the times $\tau_i$ along which the proof of Theorem 1 evaluates the lower bound.
--
--   **Formalization Note.** $Y_n$ is the corrected sum (see the definitions). The sequence $(\tau_i)$ of the page is not stated: it is "infinitely many $n$ with $Y_n\le l$", which part 2 implies when the limit is positive.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 6, proof of Theorem 1, "there exists l < ∞ such that ℙ(Y₀ > l) = ℙ(Y_j > l) < 1" and the ergodic-theorem display

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem ergodic_recurrence {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (∃ l : ℕ, 0 < P {ω | Y h ξ 0 ω ≤ l}) ∧
      ∀ l : ℕ, ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
            ∑ j ∈ Finset.Icc 1 n, ({ω | Y h ξ j ω ≤ l}.indicator (fun _ => (1 : ℝ)) ω))
          atTop (𝓝 (P.real {ω | Y h ξ 0 ω ≤ l})) := by sorry

end ScheduledQueue.Stability
