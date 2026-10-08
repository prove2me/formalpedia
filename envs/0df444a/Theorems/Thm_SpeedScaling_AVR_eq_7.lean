-- Prove2me | Theorems.Thm_SpeedScaling_AVR_eq_7
-- name    : SpeedScaling.AVR.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:43.946853+00:00
-- url     : https://prove2.me/theorems/c2aa9952-5b00-4770-8fd5-45be88caa12c
-- title:
--   Equation (7) — average-rate A-cost bounded by $F_A$
-- statement:
--   For a bitonic candidate instance and its type-A jobs, Eq. (6) defines $F_A$ by summing the executed work of jobs up to each job in the A order. The paper's inequality is
--   $$\operatorname{AVR}_A(J)\le F_A(J).$$
--
--   This is the bridge from the heuristic's energy to the quantity optimized by the canonical-instance reductions.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 379, Eq. (7).

import Definitions.Def_SpeedScaling_AVR_Canonical

namespace SpeedScaling.AVR

theorem eq_7 {n : ℕ} (J : Instance n) (S : Schedule n)
    (hS : IsOptimal (fun x : ℝ => x ^ 2) J S) (γ : Fin n → Bool)
    (hγ : IsTyping J S γ) :
    AVR_A J γ ≤ fA J S γ := by sorry

end SpeedScaling.AVR
