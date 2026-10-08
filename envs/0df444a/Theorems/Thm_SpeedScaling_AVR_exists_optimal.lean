-- Prove2me | Theorems.Thm_SpeedScaling_AVR_exists_optimal
-- name    : SpeedScaling.AVR.exists_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:55.644676+00:00
-- url     : https://prove2.me/theorems/a5572b19-4c96-4e99-a181-2b2ae9fe3ccf
-- title:
--   Existence of an optimal quadratic schedule
-- statement:
--   For every finite job instance there is a feasible piecewise-constant schedule minimizing quadratic energy:
--   $$\exists S\;\forall S'\text{ feasible},\quad E_2(S)\le E_2(S').$$
--
--   This result is implicit in the paper's optimal-schedule algorithm and supplies the existence needed when the competitive bound is compared with every feasible schedule.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, pp. 375–376, §3, Algorithm [Optimal-Schedule].

import Definitions.Def_SpeedScaling_AVR_Model

namespace SpeedScaling.AVR

theorem exists_optimal {n : ℕ} (J : Instance n) :
    ∃ S : Schedule n, IsOptimal (fun x : ℝ => x ^ 2) J S := by sorry

end SpeedScaling.AVR
