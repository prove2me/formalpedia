-- Prove2me | Theorems.Thm_PI_CntNotIntW_tensorLiftSurjective
-- name    : PI.CntNotIntW.tensorLiftSurjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:02.180255+00:00
-- url     : https://prove2.me/theorems/c08d7ef3-9057-4213-8673-c7e3c78e1bd6
-- title:
--   Cnt Not Int W: tensor Lift Surjective
-- statement:
--   The Cnt Not Int W construction uses the tensor Lift Surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/T2SpaceOfNonarchimedeanLocalField.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/T2SpaceOfNonarchimedeanLocalField.lean#L31-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_DSurjDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_T2SpaceOfNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open scoped TensorProduct
open ValuativeRel

theorem PI.CntNotIntW.tensorLiftSurjective : PiSurj := by sorry
