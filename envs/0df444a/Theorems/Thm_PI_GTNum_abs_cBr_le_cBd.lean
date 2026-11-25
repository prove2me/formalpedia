-- Prove2me | Theorems.Thm_PI_GTNum_abs_cBr_le_cBd
-- name    : PI.GTNum.abs_cBr_le_cBd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:26.221577+00:00
-- url     : https://prove2.me/theorems/d41172a9-25da-4a5d-900a-d31df1ae02df
-- title:
--   GTNum: abs c Br le c Bd
-- statement:
--   The GTNum construction uses the abs c Br le c Bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/NumMore.lean#L66-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/NumMore.lean#L66-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_NumMore
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

theorem PI.GTNum.abs_cBr_le_cBd (hI : Interlace h lam sg) :
    |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg := by sorry
