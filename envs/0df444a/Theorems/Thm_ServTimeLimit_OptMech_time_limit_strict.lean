-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_time_limit_strict
-- name    : ServTimeLimit.OptMech.time_limit_strict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:45.16157+00:00
-- url     : https://prove2.me/theorems/85f157e5-a21a-4fa9-bb9c-3a93cce56f87
-- title:
--   Proof of Theorem 1, p. 39 — for Λ1 < Λ ≤ Λ2 the first-best time limit is strictly smaller than θ̄
-- statement:
--   Assume $\Lambda, c, \bar\theta > 0$ and $\Lambda_1 < \Lambda \le \Lambda_2$. If $0 \le \theta_l \le T \le \bar\theta$ and the allocation that admits $[\theta_l, \bar\theta]$ with time $t(\theta) = \min\{\theta, T\}$ is first-best, then
--   $$T < \bar\theta .$$
--
--   Above $\Lambda_1$ the time limit is strict: some admitted customers are served for less than their ideal time.
--
--   **Formalization Note** The page's sentence continues "and it is defined by the f.o.c. $3\bar\theta - 2T - 4\theta_l(T) = 0$"; that half involves the implicit function $\theta_l(T)$ and is not formalized. For $\Lambda > \Lambda_2$ the first best has the constant shape of the case $\Lambda \ge \Lambda_2$, whose time $\widetilde T \le \bar\theta/2$ is covered by that milestone.
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), p. 39, proof of Theorem 1

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Proof of Theorem 1, p. 39: for `Λ₁ < Λ ≤ Λ₂`, the optimal time limit is strictly
smaller than `θ̄`. -/
theorem time_limit_strict (P : Params) (hP : P.Standing) (hΛ1 : lam1 P < P.Lam)
    (hΛ2 : P.Lam ≤ lam2 P) :
    ∀ θl T : ℝ, 0 ≤ θl → θl ≤ T → T ≤ P.θbar →
      IsFirstBest P (Set.Icc θl P.θbar) (fun θ => min θ T) → T < P.θbar := by sorry

end ServTimeLimit.OptMech
