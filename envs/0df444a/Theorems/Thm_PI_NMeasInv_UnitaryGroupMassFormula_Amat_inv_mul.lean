-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Amat_inv_mul
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.Amat_inv_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:50.231808+00:00
-- url     : https://prove2.me/theorems/ce09473c-c25f-4003-9f3a-05cde554fa78
-- title:
--   Unitary Group Mass Formula: Amat inv mul
-- statement:
--   The Unitary Group Mass Formula construction uses the Amat inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L226-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L226-L233

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
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
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG

theorem PI.NMeasInv.UnitaryGroupMassFormula.Amat_inv_mul (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Amat ε e f s⁻¹ * Amat ε e f s = 1 := by sorry
