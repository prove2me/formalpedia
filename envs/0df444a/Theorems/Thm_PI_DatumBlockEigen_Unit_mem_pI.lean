-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Unit_mem_pI
-- name    : PI.DatumBlockEigen.Unit.mem_pI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:19.711086+00:00
-- url     : https://prove2.me/theorems/a3892123-7080-4de0-b0ec-69ea7dbb55b8
-- title:
--   Unit: mem p I
-- statement:
--   The Unit construction uses the mem p I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L27-L33

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

theorem PI.DatumBlockEigen.Unit.mem_pI {hϖ : ϖ ∈ O} (x : O) : x ∈ pI O ϖ hϖ ↔ ∃ o ∈ O, (x : F) = ϖ * o := by sorry
