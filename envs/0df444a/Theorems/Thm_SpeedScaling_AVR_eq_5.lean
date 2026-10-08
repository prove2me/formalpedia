-- Prove2me | Theorems.Thm_SpeedScaling_AVR_eq_5
-- name    : SpeedScaling.AVR.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:35.668918+00:00
-- url     : https://prove2.me/theorems/4d5721e0-4ea2-4575-a27d-d62aa5b66709
-- title:
--   Equation (5) — split of optimal and average-rate costs
-- statement:
--   For any partition of the jobs into A and B, and an optimal quadratic schedule,
--   $$E_2(S)=\operatorname{OPT}_A+\operatorname{OPT}_B,\qquad \operatorname{AVR}(J)\le 2(\operatorname{AVR}_A+\operatorname{AVR}_B).$$
--
--   The first identity uses the one-job-at-a-time optimal schedule. The second is the square inequality applied to the two average-rate speed profiles.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 378, Eq. (5).

import Definitions.Def_SpeedScaling_AVR_Canonical

namespace SpeedScaling.AVR

theorem eq_5 {n : ℕ} (J : Instance n) (S : Schedule n)
    (hS : IsOptimal (fun x : ℝ => x ^ 2) J S) (γ : Fin n → Bool) :
    energy (fun x : ℝ => x ^ 2) J S = OPT_A J S γ + OPT_B J S γ ∧
    AVR J ≤ 2 * (AVR_A J γ + AVR_B J γ) := by sorry

end SpeedScaling.AVR
