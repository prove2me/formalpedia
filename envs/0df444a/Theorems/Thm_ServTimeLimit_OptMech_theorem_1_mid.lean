-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_theorem_1_mid
-- name    : ServTimeLimit.OptMech.theorem_1_mid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:46.422198+00:00
-- url     : https://prove2.me/theorems/423d0ae0-a5b7-4955-8547-148674148239
-- title:
--   Theorem 1 (case Λ1 ≤ Λ ≤ Λ2), p. 9 — a unique pair θl ≤ T such that admitting [θl, θ̄] with time limit T is first-best
-- statement:
--   Assume $\Lambda, c, \bar\theta > 0$ and $\Lambda_1 \le \Lambda \le \Lambda_2$, with
--   $$\Lambda_1 = \frac{32\left(4c+5-\sqrt{2c(8c+7)}\right)}{3(26c+25)\,\bar\theta},\qquad \Lambda_2 = \frac{4\left(1-\sqrt{c/(c+2)}\right)}{\bar\theta}.$$
--   Then there is a unique pair $(\theta_l, T)$ with $0 \le \theta_l \le T \le \bar\theta$ such that the allocation
--   $$t(\theta) = \begin{cases} 0 & 0 \le \theta \le \theta_l,\\ \theta & \theta_l \le \theta \le T,\\ T & T \le \theta \le \bar\theta\end{cases}$$
--   (admitted set $[\theta_l,\bar\theta]$, time $\min\{\theta, T\}$) is first-best.
--
--   Under intermediate congestion the first best imposes a time limit $T$ on the customers with the longest needs.
--
--   **Formalization Note** Uniqueness is of the pair $(\theta_l, T)$ within the displayed shape, which is what the theorem asserts. At $\Lambda = \Lambda_1$ the pair has $T = \bar\theta$ (the shape of the case $\Lambda \le \Lambda_1$), and at $\Lambda = \Lambda_2$ it has $\theta_l = T = \bar\theta/2$ (the shape of the case $\Lambda \ge \Lambda_2$).
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), p. 9, Theorem 1 (case Λ1 ≤ Λ ≤ Λ2)

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Theorem 1, case `Λ₁ ≤ Λ ≤ Λ₂` (p. 9): there is a unique pair `(θ_l, T)` with
`0 ≤ θ_l ≤ T ≤ θ̄` such that admitting `[θ_l, θ̄]` with the time limit `t(θ) = min{θ, T}` is
first-best. -/
theorem theorem_1_mid (P : Params) (hP : P.Standing) (hΛ1 : lam1 P ≤ P.Lam)
    (hΛ2 : P.Lam ≤ lam2 P) :
    ∃! q : ℝ × ℝ, (0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ P.θbar) ∧
      IsFirstBest P (Set.Icc q.1 P.θbar) (fun θ => min θ q.2) := by sorry

end ServTimeLimit.OptMech
