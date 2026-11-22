-- Prove2me | Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_epsI_piI
-- name    : PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_piI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:24.261795+00:00
-- url     : https://prove2.me/theorems/7280429a-a13d-40c1-ab8c-7e16bb0f8d9d
-- title:
--   SW: eps I pi I
-- statement:
--   The SW construction uses the eps I pi I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean#L29-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ}

theorem PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_piI (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by sorry
