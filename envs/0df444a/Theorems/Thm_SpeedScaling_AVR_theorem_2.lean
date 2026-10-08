-- Prove2me | Theorems.Thm_SpeedScaling_AVR_theorem_2
-- name    : SpeedScaling.AVR.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:56.044276+00:00
-- url     : https://prove2.me/theorems/ef67a40d-898e-4212-9e72-4f1ef12e23c0
-- title:
--   Theorem 2 — quadratic AVR competitive ratio between four and eight
-- statement:
--   For quadratic power $P(s)=s^2$, the Average Rate Heuristic has competitive ratio $r$ with
--   $$4\le r\le 8.$$
--
--   The upper bound says $\operatorname{AVR}(J)\le8E_2(S)$ for every instance and every feasible schedule $S$. The lower bound says that for every $c<4$ there is an instance and feasible schedule with $\operatorname{AVR}(J)>cE_2(S)$. These quantified inequalities express the least upper bound of the ratios without an empty-set or division convention.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 381, Theorem 2.

import Definitions.Def_SpeedScaling_AVR_Model

namespace SpeedScaling.AVR

theorem theorem_2 :
    (∀ (n : ℕ) (J : Instance n) (S : Schedule n),
      IsSchedule J S → Feasible J S →
        AVR J ≤ 8 * energy (fun x : ℝ => x ^ 2) J S) ∧
    (∀ c : ℝ, c < 4 →
      ∃ (n : ℕ) (J : Instance n) (S : Schedule n),
        IsSchedule J S ∧ Feasible J S ∧
        c * energy (fun x : ℝ => x ^ 2) J S < AVR J) := by sorry

end SpeedScaling.AVR
