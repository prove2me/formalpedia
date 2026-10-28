-- Prove2me | Theorems.Thm_ScheduledQueue_Stability_Y_gamma2_finite
-- name    : ScheduledQueue.Stability.Y_gamma2_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:03.010004+00:00
-- url     : https://prove2.me/theorems/20b4edb7-d1c0-485f-8be4-232106093b7a
-- title:
--   Proof of Theorem 1, pp. 6–7 — Y_n < ∞ for all n and Γ₂ < ∞ a.s.
-- statement:
--   In the scheduled-traffic model with $h>0$, i.i.d. integrable perturbations $(\xi_j)_{j\in\mathbb Z}$ and an independent uniform shift $U$, let
--   $$Y_n=\sum_{j\ge1} I\big(-\xi_{n+1-j}>(j-2)h\big)\quad(n=0,1,2,\dots),\qquad \Gamma_2=\sum_{j\ge1} I\big(\xi_j\ge(j-1)h\big).$$
--   Then, almost surely, $Y_n<\infty$ for every $n$ and $\Gamma_2<\infty$.
--
--   $Y_n$ bounds the number of customers scheduled in $\{1,\dots,n\}$ that arrive (in reversed time) after $nh$, and $\Gamma_2$ the number of customers $j\ge1$ that arrive (in reversed time) at or before $0$. Their finiteness uses $\mathbb E\xi_0^-<\infty$ and $\mathbb E\xi_0^+<\infty$ respectively.
--
--   **Formalization Note.** The counts are valued in $\mathbb N\cup\{\infty\}$, so finiteness is real content. $Y_n$ is the corrected form of the page's $\sum_{j\ge1}I(\xi_{k(s)-j}>(j-2)h)$, whose sign is misprinted (the page's own justification "since $\mathbb E\xi_0^-<\infty$" requires $-\xi$) and which omits $\xi_{k(s)}$. The page proves $Y_0<\infty$ a.s.; the statement for all $n$ at once follows because each $Y_n$ has the law of $Y_0$ and there are countably many.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, p. 6, "Since 𝔼ξ₀⁻ < ∞, Y₀ < ∞ a.s." (Y corrected) and pp. 6–7, display defining Γ₂ ("Γ₂ < ∞ a.s. since 𝔼ξ₀⁺ < ∞")

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace ScheduledQueue.Stability

theorem Y_gamma2_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, (∀ n : ℕ, Y h ξ n ω < ⊤) ∧ gamma2 h ξ ω < ⊤ := by sorry

end ScheduledQueue.Stability
