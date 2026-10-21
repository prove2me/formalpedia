-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_subproblem_4
-- name    : ServTimeLimit.OptMech.subproblem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:41.860308+00:00
-- url     : https://prove2.me/theorems/70d4e24a-ad50-4459-8cc1-9e39003d312c
-- title:
--   Sub-problem (4), pp. 35–36 — minimising ∫t² on [a, b] given ∫t = k and t ≤ θ: the constant k/(b−a) or the time limit min{θ, T}, T = b − √(b² − a² − 2k)
-- statement:
--   Let $0 \le a < b$ and $k \ge 0$. Consider sub-problem (4) of the proof of Theorem 1:
--   $$\min_{t:[a,b]\to\mathbb R_+} \int_a^b t(\theta)^2\, d\theta \quad\text{s.t.}\quad \int_a^b t(\theta)\, d\theta = k,\qquad t(\theta) \le \theta \ \ \forall \theta,$$
--   over measurable $t$ with $0 \le t(\theta) \le \theta$ on $[a,b]$.
--
--   1. If $k \le a(b-a)$, the constant $t \equiv k/(b-a)$ is feasible, and every feasible $t$ has $\int_a^b t^2 \ge \int_a^b (k/(b-a))^2$, with equality only if $t = k/(b-a)$ almost everywhere on $[a,b]$.
--   2. If $a(b-a) \le k \le (b^2-a^2)/2$, put $T = b - \sqrt{b^2-a^2-2k}$. Then $a \le T \le b$, the time-limit function
--   $$t^*(\theta) = \begin{cases}\theta & a \le \theta \le T,\\ T & T \le \theta \le b,\end{cases}$$
--   i.e. $t^*(\theta) = \min\{\theta, T\}$, satisfies $\int_a^b t^* = k$, and every feasible $t$ has $\int_a^b t^2 \ge \int_a^b (t^*)^2$, with equality only if $t = t^*$ almost everywhere on $[a,b]$.
--
--   This is the reduction step of the proof of Theorem 1: for a fixed admitted interval and a fixed load, the waiting time is minimised by a time limit, which is why first-best time functions have the shape $\min\{\theta, T\}$.
--
--   **Formalization Note** The paper's "unique solution" is read up to a null set, since $\int t^2$ does not see changes of $t$ on null sets. The page states uniqueness for the second case; the first case's "the solution" is read in the same way.
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), pp. 35–36, proof of Theorem 1, sub-problem (4) and its solution

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Sub-problem (4) and its solution (proof of Theorem 1, pp. 35–36): on `[a, b]`, among
measurable `t` with `0 ≤ t(θ) ≤ θ` and `∫_a^b t = k`, the integral `∫_a^b t²` is minimised by the
constant `k/(b − a)` when `k ≤ a(b − a)`, and by `min{θ, T}` with `T = b − √(b² − a² − 2k)` when
`a(b − a) ≤ k ≤ (b² − a²)/2`; the minimiser is unique up to a null set. -/
theorem subproblem_4 (a b k : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    (0 ≤ k → k ≤ a * (b - a) →
      (∀ θ ∈ Set.Icc a b, 0 ≤ k / (b - a) ∧ k / (b - a) ≤ θ) ∧
      (∫ _θ in Set.Icc a b, k / (b - a)) = k ∧
      ∀ t : ℝ → ℝ, Measurable t → (∀ θ ∈ Set.Icc a b, 0 ≤ t θ ∧ t θ ≤ θ) →
        (∫ θ in Set.Icc a b, t θ) = k →
        (∫ _θ in Set.Icc a b, (k / (b - a)) ^ 2) ≤ ∫ θ in Set.Icc a b, t θ ^ 2 ∧
        ((∫ _θ in Set.Icc a b, (k / (b - a)) ^ 2) = ∫ θ in Set.Icc a b, t θ ^ 2 →
          t =ᵐ[volume.restrict (Set.Icc a b)] fun _ => k / (b - a))) ∧
    (a * (b - a) ≤ k → k ≤ (b ^ 2 - a ^ 2) / 2 →
      ∀ T : ℝ, T = b - Real.sqrt (b ^ 2 - a ^ 2 - 2 * k) →
      a ≤ T ∧ T ≤ b ∧
      (∫ θ in Set.Icc a b, min θ T) = k ∧
      ∀ t : ℝ → ℝ, Measurable t → (∀ θ ∈ Set.Icc a b, 0 ≤ t θ ∧ t θ ≤ θ) →
        (∫ θ in Set.Icc a b, t θ) = k →
        (∫ θ in Set.Icc a b, (min θ T) ^ 2) ≤ ∫ θ in Set.Icc a b, t θ ^ 2 ∧
        ((∫ θ in Set.Icc a b, (min θ T) ^ 2) = ∫ θ in Set.Icc a b, t θ ^ 2 →
          t =ᵐ[volume.restrict (Set.Icc a b)] fun θ => min θ T)) := by sorry

end ServTimeLimit.OptMech
