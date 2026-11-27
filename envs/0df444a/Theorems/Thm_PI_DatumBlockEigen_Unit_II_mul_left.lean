-- Prove2me | Theorems.Thm_PI_DatumBlockEigen_Unit_II_mul_left
-- name    : PI.DatumBlockEigen.Unit.II_mul_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:17.095075+00:00
-- url     : https://prove2.me/theorems/41c36d57-f35c-4628-999e-aead874bad9e
-- title:
--   Unit: II mul left
-- statement:
--   The Unit construction uses the II mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/IsIntInvOfUnit.lean#L107-L113

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

theorem PI.DatumBlockEigen.Unit.II_mul_left {p q r : ℕ} {y : Matrix (Fin q) (Fin r) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)
    {g : Matrix (Fin p) (Fin q) F} (hg : ∀ i j, g i j ∈ O) : g * y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by sorry
