-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_tildeY_pos
-- name    : ScheduledQueue.Stability.tildeY_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:04.172401+00:00
-- url     : https://prove2.me/theorems/2e68e8ec-4cb4-432f-914a-8560542e870e
-- title:
--   Proof of Theorem 1, p. 6 — if ξ₀⁺ is unbounded, then ℙ(Ỹ₀ > r) > 0 for every r
-- statement:
--   In the scheduled-traffic model with $h>0$, i.i.d. integrable perturbations $(\xi_j)_{j\in\mathbb Z}$ and an independent uniform shift $U$, suppose that $\xi_0^+$ is not a bounded random variable: there is no constant $c$ with $\xi_0\le c$ almost surely. Let $\tilde Y_0=\sum_{j\ge1}I(\xi_j^+\ge(j+2)h)$. Then for every $r\in\{0,1,2,\dots\}$,
--   $$\mathbb P\big(\tilde Y_0>r\big)>0 .$$
--
--   Unbounded perturbations make it possible, with positive probability, for arbitrarily many customers scheduled just after a given time to be delayed far enough to count in the lower bound of the proof of Theorem 1.
--
--   **Formalization Note.** The page's hypothesis "$\xi_0^+$ has infinite support" is read as the negation of the theorem's condition "$\xi_0^+$ is a bounded rv", i.e. $\neg\,\exists c,\ \xi_0\le c$ a.s. $\tilde Y_0$ is valued in $\mathbb N\cup\{\infty\}$.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 6, proof of Theorem 1, "For each r ∈ ℤ₊, the infinite support of ξ₀⁺ implies that ℙ(Ỹ₀ > r) = ℙ(Ỹᵢ > r) > 0"

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem tildeY_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (¬ ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) →
      ∀ r : ℕ, 0 < P {ω | (r : ℕ∞) < tildeY h ξ 0 ω} := by sorry

end ScheduledQueue.Stability
