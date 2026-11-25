-- Prove2me | Theorems.Thm_PI_GTNum_abs_cBr_le_top
-- name    : PI.GTNum.abs_cBr_le_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:31:23.875715+00:00
-- url     : https://prove2.me/theorems/5da5b194-5503-441c-850c-2d78bbf9d235
-- title:
--   GTNum: abs c Br le top
-- statement:
--   The GTNum construction uses the abs c Br le top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/NumMore.lean#L46-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/NumMore.lean#L46-L64

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

theorem PI.GTNum.abs_cBr_le_top (hI : Interlace h lam sg) :
    |cBr h lam sg| ≤ (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^
      (n * ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card) := by sorry
