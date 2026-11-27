-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Unit_shiftJ
-- name    : PI.DatumBlockEigen.Unit.shiftJ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:02.09802+00:00
-- url     : https://prove2.me/theorems/ba6e37d8-5409-4e32-9fec-e94d2cc022dd
-- title:
--   Unit: shift J
-- statement:
--   The Unit construction uses the shift J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L147-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L147-L170

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
variable {O ϖ}

theorem PI.DatumBlockEigen.Unit.shiftJ (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hL : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a : ℕ}
    {J' : Subgroup (GL (Fin a) F)} (hK : Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J')
    (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) (g : J') (y : Matrix (Fin a) (Fin a) F)
    (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) :
    ∃ U : J', (U : GL (Fin a) F) ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a ∧
      (((g * U : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) =
        ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) + y := by sorry
