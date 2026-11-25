-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_nb
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.nb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:14:16.864988+00:00
-- url     : https://prove2.me/theorems/a20bfaf1-e622-5167-a5a7-a3e6afb7b7b4
-- title:
--   Unitary Group Mass Formula: nb
-- statement:
--   The Unitary Group Mass Formula construction uses the nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/ConjSubMulVec.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/ConjSubMulVec.lean#L102-L106

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
variable (hG : Gram ε e f)
include hG
omit hG

theorem PI.NMeasInv.UnitaryGroupMassFormula.nb {κ lam : ℝ} {x : ℂ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ lam⁻¹ ∨ x = 0) : ‖(κ : ℂ) * x‖ ≤ lam⁻¹ * ‖x‖ := by sorry
