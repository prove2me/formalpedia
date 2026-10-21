-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_theorem_1_low
-- name    : ServTimeLimit.OptMech.theorem_1_low
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:48.85711+00:00
-- url     : https://prove2.me/theorems/fcfcdb7c-6761-4a4b-ab04-d63ee4d2b800
-- title:
--   Theorem 1 (case Λ ≤ Λ1), p. 8 — a unique θl such that admitting [θl, θ̄] with t(θ) = θ is first-best
-- statement:
--   Assume $\Lambda, c, \bar\theta > 0$ and
--   $$\Lambda \le \Lambda_1 = \frac{32\left(4c+5-\sqrt{2c(8c+7)}\right)}{3(26c+25)\,\bar\theta}.$$
--   Then there is a unique type $\theta_l \in [0,\bar\theta]$ such that the allocation
--   $$t(\theta) = \begin{cases} 0 & 0 \le \theta \le \theta_l,\\ \theta & \theta_l \le \theta \le \bar\theta\end{cases}$$
--   (admitted set $[\theta_l, \bar\theta]$, every admitted customer served for her full need) is first-best.
--
--   Under low congestion the first best uses admission control only: no time limit.
--
--   **Formalization Note** Uniqueness is of $\theta_l$ within the displayed shape, which is what the theorem asserts; changing $t$ on a null set, or the endpoints of the admitted interval, gives other maximisers with the same welfare. The printed "$/3(26c+25)\bar\theta$" is read as division by $3(26c+25)\bar\theta$, as the display on p. 39 settles.
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), p. 8, Theorem 1 (case Λ ≤ Λ1)

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Theorem 1, case `Λ ≤ Λ₁` (p. 8): there is a unique type `θ_l ∈ [0, θ̄]` such that
admitting `[θ_l, θ̄]` with `t(θ) = θ` is first-best. -/
theorem theorem_1_low (P : Params) (hP : P.Standing) (hΛ : P.Lam ≤ lam1 P) :
    ∃! θl : ℝ, (0 ≤ θl ∧ θl ≤ P.θbar) ∧
      IsFirstBest P (Set.Icc θl P.θbar) (fun θ => θ) := by sorry

end ServTimeLimit.OptMech
