-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Unit_II_add
-- name    : PI.DatumBlockEigen.Unit.II_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:19.133287+00:00
-- url     : https://prove2.me/theorems/fccae46f-e75d-4e37-9cfe-41596e8fade9
-- title:
--   Unit: II add
-- statement:
--   The Unit construction uses the II add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L115-L120

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

theorem PI.DatumBlockEigen.Unit.II_add {p q : ℕ} {y z : Matrix (Fin p) (Fin q) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)
    (hz : z ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) : y + z ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by sorry
