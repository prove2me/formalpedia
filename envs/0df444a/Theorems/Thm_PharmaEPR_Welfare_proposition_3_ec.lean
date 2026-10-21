-- Prove2me | Theorems.Thm_PharmaEPR_Welfare_proposition_3_ec
-- name    : PharmaEPR.Welfare.proposition_3_ec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:27.47795+00:00
-- url     : https://prove2.me/theorems/8aab9329-d8d7-45f5-9b0d-f488d7ed3dc1
-- title:
--   Proposition 3, p. 17 (EC half) — environmental threshold for eliminating over-prescription
-- statement:
--   Suppose $u_p\ge\bar u_p^{EC}$ and $k\ge\bar k(u_p)$ in the stated regime. There is a threshold $\bar\epsilon_e^{EC}(\epsilon_s)$, nonincreasing as the social disutility $\epsilon_s\ge0$ increases, such that for every environmental disutility $\epsilon_e\ge0$:
--
--   $$\text{an EC welfare optimum avoids over-prescription}
--     \quad\Longleftrightarrow\quad
--     \epsilon_e\ge\bar\epsilon_e^{EC}(\epsilon_s).$$
--
--   This is the EC part of Proposition 3, used to identify when avoiding over-prescription is worth the welfare cost. The appendix gives its threshold by cases; monotonicity states the content of the displayed nonpositive derivative without requiring differentiability at a case boundary.
--
--   **Formalization Note** The SR half is asserted without a proof in the appendix and is outside this milestone. The left side means that the attained EC optimal welfare belongs to the set of feasible equilibrium welfare values without over-prescription.
-- source:
--   Alev, Atasu, Toktay & Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020-09-05 posting), p. 17, Proposition 3, EC half; proof Online Appendix pp. 2–3

import Mathlib
import Definitions.Def_PharmaEPR_Welfare_Model

namespace PharmaEPR.Welfare

theorem proposition_3_ec (P : Params) (hP : Regime P)
    (hu : uEC P ≤ P.up) (hk : kBar P ≤ P.k) :
    ∃ epsBar : ℝ → ℝ,
      AntitoneOn epsBar (Set.Ici (0 : ℝ)) ∧
      ∀ es : ℝ, 0 ≤ es → ∀ e : ℝ, 0 ≤ e →
        let Q : Params := { P with epsE := e, epsS := es }
        IsGreatest (achievable Q .EC) (optW Q .EC) ∧
        (optW Q .EC ∈ achievableNoOP Q .EC ↔ epsBar es ≤ e) := by sorry

end PharmaEPR.Welfare
