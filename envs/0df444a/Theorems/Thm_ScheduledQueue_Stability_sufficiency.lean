-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_sufficiency
-- name    : ScheduledQueue.Stability.sufficiency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:59.49599+00:00
-- url     : https://prove2.me/theorems/d3971131-b3ab-43c3-b827-c1da354a1629
-- title:
--   Proof of Theorem 1, p. 6 — if ξ₀⁺ is bounded, then M(∞) = sup_{s≥0} (Λ(s) − s) < ∞ a.s.
-- statement:
--   In the scheduled-traffic model with $h>0$, i.i.d. integrable perturbations $(\xi_j)_{j\in\mathbb Z}$ and an independent uniform shift $U$, suppose that $\xi_0^+$ is a bounded random variable, i.e. $\xi_0\le c$ almost surely for some constant $c$. Then almost surely the reversed counts $\#\{j: jh+Uh-\xi_j\in(0,s]\}$ are finite for every $s\ge0$ and
--   $$M(\infty)=\sup_{s\ge0}\big(\Lambda(s)-s\big)<\infty .$$
--
--   Since $M(t)$ is nondecreasing in $t$ and has the law of the workload $W(t)$, this gives the "if" direction of Theorem 1: $W(t)$ converges in distribution to the finite random variable $M(\infty)$.
--
--   **Formalization Note.** "$M(\infty)<\infty$" is stated as the existence, for almost every outcome, of a real $C$ with $\Lambda(s)-s\le C$ for all $s\ge0$. The conjunct that every reversed count is finite rules out the junk value $0$ that $\Lambda$ takes on an infinite count.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 6, proof of Theorem 1, "But if ξ₀⁺ ≤ c < ∞ a.s., then … and hence M(∞) < ∞ a.s."

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem sufficiency {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) →
      ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → revCount h ξ U s ω ≠ ⊤ ∧ Lam h ξ U s ω - s ≤ C := by sorry

end ScheduledQueue.Stability
