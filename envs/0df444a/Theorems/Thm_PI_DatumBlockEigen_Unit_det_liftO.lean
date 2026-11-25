-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Unit_det_liftO
-- name    : PI.DatumBlockEigen.Unit.det_liftO
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:56.396372+00:00
-- url     : https://prove2.me/theorems/0872aa92-e81f-4c81-906c-71f0f8f918ef
-- title:
--   Unit: det lift O
-- statement:
--   The Unit construction uses the det lift O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L19-L23

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

theorem PI.DatumBlockEigen.Unit.det_liftO {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n F)
    (h : ∀ i j, N i j ∈ O) : ((liftO O N h).det : F) = N.det := by sorry
