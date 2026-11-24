-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hJ_sub_right
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.hJ_sub_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:31:53.855217+00:00
-- url     : https://prove2.me/theorems/7e85c57d-2e17-4949-b48a-19a935eae750
-- title:
--   Unitary Group Mass Formula: h J sub right
-- statement:
--   The Unitary Group Mass Formula construction uses the h J sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousHPart.lean#L53-L54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
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
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε}

theorem PI.ScMuExists.UnitaryGroupMassFormula.hJ_sub_right (u x y : Fin n → ℂ) : hJ ε u (x - y) = hJ ε u x - hJ ε u y := by sorry
