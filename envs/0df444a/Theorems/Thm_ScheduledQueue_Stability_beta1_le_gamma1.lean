-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_beta1_le_gamma1
-- name    : ScheduledQueue.Stability.beta1_le_gamma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:52.27898+00:00
-- url     : https://prove2.me/theorems/57257fb1-141d-490a-ac31-c92b4e43e40f
-- title:
--   Proof of Theorem 1, p. 5 — β₁(s) ≤ Γ₁ and 𝔼Γ₁ < ∞
-- statement:
--   In the scheduled-traffic model with $h>0$, i.i.d. integrable perturbations $(\xi_j)_{j\in\mathbb Z}$ and an independent uniform shift $U$, let
--   $$\beta_1(s)=\sum_{j\ge1} I\big(Uh-jh-\xi_{-j}\in(0,s]\big),\qquad \Gamma_1=\sum_{j\ge1} I\big(-\xi_{-j}>(j-1)h\big).$$
--   Then:
--
--   1. for every outcome with $U\in[0,1]$ and every $s$, $\beta_1(s)\le\Gamma_1$;
--   2. $\mathbb E\,\Gamma_1<\infty$.
--
--   In particular $\max_{s\ge0}\beta_1(s)\le\Gamma_1<\infty$ almost surely: only finitely many customers scheduled before time $0$ arrive (in reversed time) after time $0$. This is the first half of the upper bound on $M(\infty)$.
--
--   **Formalization Note.** The counts are valued in $\mathbb N\cup\{\infty\}$ and the expectation is the lower Lebesgue integral of $\Gamma_1$ as an extended nonnegative real. The pointwise inequality is stated for every outcome on which $U\in[0,1]$.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 5, proof of Theorem 1, display defining Γ₁ and the sentence after it

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem beta1_le_gamma1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (∀ ω, U ω ∈ Icc (0 : ℝ) 1 → ∀ s : ℝ, beta1 h ξ U s ω ≤ gamma1 h ξ ω) ∧
      ∫⁻ ω, (gamma1 h ξ ω : ℝ≥0∞) ∂P < ∞ := by sorry

end ScheduledQueue.Stability
