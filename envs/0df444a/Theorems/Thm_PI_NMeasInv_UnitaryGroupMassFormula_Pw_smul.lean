-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_smul
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.Pw_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:16:33.679953+00:00
-- url     : https://prove2.me/theorems/ef44f0af-de6a-499b-b3b1-729b32b1327a
-- title:
--   Unitary Group Mass Formula: Pw smul
-- statement:
--   The Unitary Group Mass Formula construction uses the Pw smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/ConjSubMulVec.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/ConjSubMulVec.lean#L21-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
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
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}

theorem PI.NMeasInv.UnitaryGroupMassFormula.Pw_smul (c : ℂ) (x : Fin n → ℂ) : Pw ε e f (c • x) = c • Pw ε e f x := by sorry
