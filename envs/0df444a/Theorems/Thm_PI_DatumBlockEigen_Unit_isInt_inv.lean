-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Unit_isInt_inv
-- name    : PI.DatumBlockEigen.Unit.isInt_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:13.024084+00:00
-- url     : https://prove2.me/theorems/2c3c969f-06fe-5d1e-a9f9-9064ea40cd50
-- title:
--   Unit: is Int inv
-- statement:
--   The Unit construction uses the is Int inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L62-L68

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
variable (O)

theorem PI.DatumBlockEigen.Unit.isInt_inv {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n F)
    (hN : ∀ i j, N i j ∈ O) (hdi : N.det⁻¹ ∈ O) : ∀ i j, N⁻¹ i j ∈ O := by sorry
