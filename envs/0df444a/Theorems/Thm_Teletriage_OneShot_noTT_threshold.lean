-- Prove2me | Theorems.Thm_Teletriage_OneShot_noTT_threshold
-- name    : Teletriage.OneShot.noTT_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:30.410038+00:00
-- url     : https://prove2.me/theorems/8cd8d8fe-18f2-49ab-8b7f-0601043d9b8c
-- title:
--   §4.1, p. 10 (PDF 10) — without teletriage the patient goes to the ED iff b ≥ b0 = 1 − c_P/c_E
-- statement:
--   Consider the one-shot open-access model with copays $0<c_P<c_E$ and no teletriage. A patient with belief $b\in[0,1]$ (the probability that she is critical) chooses between the ED, at cost $c_E$, and the PCP, at expected cost $c_P+b\,c_E$, and goes to the ED on a tie. Then, for every such belief $b$,
--   $$\text{the patient goes to the ED}\iff b\ \ge\ b_0=1-\frac{c_P}{c_E},$$
--   and to the PCP otherwise.
--
--   This threshold rule is the baseline against which the effect of teletriage is measured.
--
--   **Formalization Note** The statement is about the argmin action of (1) with ED chosen on a tie; it carries the standing assumptions of the mission.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. 10 (PDF 10), §4.1

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- §4.1, p. 10: without teletriage the patient goes to the ED exactly when `b ≥ b0`. -/
theorem noTT_threshold (P : Params) (hS : P.Standing) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    actNoTT P b = .ED ↔ b0 P ≤ b := by sorry

end Teletriage.OneShot
