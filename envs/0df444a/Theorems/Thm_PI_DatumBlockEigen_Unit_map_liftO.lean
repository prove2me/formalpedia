-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Unit_map_liftO
-- name    : PI.DatumBlockEigen.Unit.map_liftO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:20.624665+00:00
-- url     : https://prove2.me/theorems/d750282c-c262-4cb7-9baf-8c53dc51ca9d
-- title:
--   Unit: map lift O
-- statement:
--   The Unit construction uses the map lift O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L15-L17

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

theorem PI.DatumBlockEigen.Unit.map_liftO {m n : Type} (N : Matrix m n F) (h : ∀ i j, N i j ∈ O) :
    (liftO O N h).map O.subtype = N := by sorry
