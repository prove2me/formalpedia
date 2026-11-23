-- Prove2me | Theorems.Thm_PI_WGL_XiA_rowsZ_strictMono
-- name    : PI.WGL.XiA.rowsZ_strictMono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:25.450822+00:00
-- url     : https://prove2.me/theorems/2817ca7e-dcfb-43a1-a48a-56a1f5e4b4dc
-- title:
--   Xi A: rows Z strict Mono
-- statement:
--   The Xi A construction uses the rows Z strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/RowsZStrictMono.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/RowsZStrictMono.lean#L74-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.XiA.rowsZ_strictMono {n N : ℕ} (h : n + 1 = N) (i : Fin n) : StrictMono (rowsZ h i) := by sorry
