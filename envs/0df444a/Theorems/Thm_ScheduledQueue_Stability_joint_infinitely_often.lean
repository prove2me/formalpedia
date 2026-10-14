-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_joint_infinitely_often
-- name    : ScheduledQueue.Stability.joint_infinitely_often
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:11.560978+00:00
-- url     : https://prove2.me/theorems/bd5952f6-a831-4586-a747-48a583c37b75
-- title:
--   Proof of Theorem 1, p. 6 — conclusion of the Borel–Cantelli step: Y_n ≤ l and Ỹ_n > r infinitely often a.s.
-- statement:
--   In the scheduled-traffic model with $h>0$, i.i.d. integrable perturbations $(\xi_j)_{j\in\mathbb Z}$ and an independent uniform shift $U$, suppose that $\xi_0^+$ is not a bounded random variable. Let $l,r\in\{0,1,2,\dots\}$ with $\mathbb P(Y_0\le l)>0$. Then almost surely there are infinitely many $n\in\{0,1,2,\dots\}$ with
--   $$Y_n\le l\qquad\text{and}\qquad \tilde Y_n>r .$$
--
--   Along such $n$, the lower decomposition gives $\Lambda(nh)-nh\ge h(r-l-\Gamma_2)$, which is how the proof of Theorem 1 shows that $M(\infty)=\infty$ when the perturbations are unbounded above.
--
--   **Formalization Note.** This is the conclusion of the page's conditional Borel–Cantelli argument along the times $\tau_i$, restated without the $\tau_i$ as "infinitely often in $n$". The printed argument conditions on $\mathcal F_{\tau_i}$ events $\{\tilde Y_{\tau_i}>r\}$ that look into the future, so it does not apply as written; the conclusion stated here is nevertheless true. $Y_n$ is the corrected sum of the definitions.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 6, proof of Theorem 1, conclusion of "It follows from the conditional Borel Cantelli lemma (see, Doob (1953)) that β₂(τᵢh) > r infinitely often a.s."

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem joint_infinitely_often {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (¬ ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) →
      ∀ l r : ℕ, 0 < P {ω | Y h ξ 0 ω ≤ l} →
        ∀ᵐ ω ∂P, ∃ᶠ n : ℕ in atTop, Y h ξ n ω ≤ l ∧ (r : ℕ∞) < tildeY h ξ n ω := by sorry

end ScheduledQueue.Stability
