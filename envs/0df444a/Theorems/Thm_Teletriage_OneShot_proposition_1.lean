-- Prove2me | Theorems.Thm_Teletriage_OneShot_proposition_1
-- name    : Teletriage.OneShot.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:48.240837+00:00
-- url     : https://prove2.me/theorems/3a526716-8288-4efc-9344-133805191294
-- title:
--   Proposition 1, p. 9 (PDF 9) — if 0 < b < 1 and α + β < 1 then teletriage is informative: b_PS < b < b_PC
-- statement:
--   Let teletriage have undertriage rate $\alpha=\Pr(PS\mid C)\in[0,1]$ and overtriage rate $\beta=\Pr(PC\mid S)\in[0,1]$, and let a patient with belief $b$ update to $b_{PS}$ after the prediction *sick* and to $b_{PC}$ after the prediction *critical*, by Bayes' rule (10). If $0<b<1$ and $\alpha+\beta<1$, then
--   $$b_{PS}\ <\ b\ <\ b_{PC},$$
--   that is, teletriage is informative: a prediction of sickness lowers the belief of being critical and a prediction of criticality raises it.
--
--   This is the informative case of Proposition 1; it is what makes the posteriors straddle the belief in the proof of Proposition 2.
--
--   **Formalization Note** Only the first sentence of Proposition 1 (the informative case) is formalized; the uninformative and worse-than-guessing cases are not part of this mission.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. 9 (PDF 9), Proposition 1

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Proposition 1 (informative case), p. 9: if `0 < b < 1` and `α + β < 1` then
`bPS < b < bPC`. -/
theorem proposition_1 (P : Params) (hS : P.Standing) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hI : P.Informative) : bPS P b < b ∧ b < bPC P b := by sorry

end Teletriage.OneShot
