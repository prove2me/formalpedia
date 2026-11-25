-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_algValsFin_main
-- name    : PI.AlgValsFin.W.algValsFin_main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:15.854815+00:00
-- url     : https://prove2.me/theorems/af3cd654-effb-479e-acbf-f20b48d66bbb
-- title:
--   W: alg Vals Fin main
-- statement:
--   The W construction uses the alg Vals Fin main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/AlgValsFinMain.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/AlgValsFinMain.lean#L12-L13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinOfTors
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_TorsUnitsOfNbhd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AlgValsFin PI.AlgValsFin.W

theorem PI.AlgValsFin.W.algValsFin_main (L : Type) [Field L] [NumberField L] : AlgValsFin L := by sorry
