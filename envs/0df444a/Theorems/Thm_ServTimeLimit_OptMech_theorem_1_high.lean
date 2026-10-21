-- Prove2me | Theorems.Thm_ServTimeLimit_OptMech_theorem_1_high
-- name    : ServTimeLimit.OptMech.theorem_1_high
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:56.411496+00:00
-- url     : https://prove2.me/theorems/7a914d19-2c70-4c28-95a3-29e960d57fb5
-- title:
--   Theorem 1 (case Λ ≥ Λ2), p. 9 — admitting [T̃, 2T̃] with time T̃ is first-best, with welfare (c+2)(1−√(c/(c+2)))²/2
-- statement:
--   Assume $\Lambda, c, \bar\theta > 0$ and $\Lambda \ge \Lambda_2 = 4\left(1-\sqrt{c/(c+2)}\right)/\bar\theta$, and let
--   $$\widetilde T = \sqrt{\frac{\bar\theta}{\Lambda}\left(1-\sqrt{\frac{c}{c+2}}\right)} .$$
--   Then $2\widetilde T \le \bar\theta$, the allocation
--   $$t(\theta) = \begin{cases} \widetilde T & \widetilde T \le \theta \le 2\widetilde T,\\ 0 & \text{otherwise}\end{cases}$$
--   (admitted set $[\widetilde T, 2\widetilde T]$, constant time $\widetilde T$) is first-best, and its social welfare is
--   $$\mathcal{FB} = \frac12 (c+2)\left(1-\sqrt{\frac{c}{c+2}}\right)^2 .$$
--
--   Under very high congestion the first best gives every admitted customer the same time: the time limit binds for everyone.
--
--   **Formalization Note** The first-best value is taken from the end of the proof of Theorem 1 (p. 39). No uniqueness is claimed, and none holds: welfare of a constant-time allocation depends only on the product of the time and the measure of the admitted set, so for instance $[\bar\theta-\widetilde T, \bar\theta]$ with time $\widetilde T$ is first-best as well. Theorem 1 asserts uniqueness only in its other two cases.
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), p. 9, Theorem 1 (case Λ ≥ Λ2), with the first-best value from p. 39 (proof of Theorem 1)

import Mathlib
import Definitions.Def_ServTimeLimit_OptMech_Model

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Theorem 1, case `Λ ≥ Λ₂` (p. 9), with the first-best value from p. 39: admitting
`[T̃, 2T̃]` with time `T̃` for everyone admitted is first-best, and its welfare is
`(c + 2)(1 − √(c/(c + 2)))²/2`. -/
theorem theorem_1_high (P : Params) (hP : P.Standing) (hΛ : lam2 P ≤ P.Lam) :
    2 * Ttilde P ≤ P.θbar ∧
    IsFirstBest P (Set.Icc (Ttilde P) (2 * Ttilde P)) (fun _ => Ttilde P) ∧
    welfare P (Set.Icc (Ttilde P) (2 * Ttilde P)) (fun _ => Ttilde P) = fbValue P := by sorry

end ServTimeLimit.OptMech
