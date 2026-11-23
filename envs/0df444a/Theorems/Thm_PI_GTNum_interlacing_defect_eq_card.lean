-- Prove2me | Theorems.Thm_PI_GTNum_interlacing_defect_eq_card
-- name    : PI.GTNum.interlacing_defect_eq_card
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:01.958552+00:00
-- url     : https://prove2.me/theorems/9c92d25a-f19f-4e07-b2e7-7e07ec32a6ca
-- title:
--   GTNum: interlacing defect eq card
-- statement:
--   The GTNum construction uses the interlacing defect eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/InterlacingDefectEqCard.lean#L74-L78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTNum
open Formalism.BasicNotions PI Finset
variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)

theorem PI.GTNum.interlacing_defect_eq_card (hI : Interlace h lam sg) :
    D1 h lam sg = ((∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card : ℕ) : ℤ) := by sorry
