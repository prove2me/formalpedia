-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Alin_apply
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.Alin_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:15:47.609074+00:00
-- url     : https://prove2.me/theorems/f6f62b6f-91b8-43e3-9fed-31b9b07a0019
-- title:
--   Unitary Group Mass Formula: Alin apply
-- statement:
--   The Unitary Group Mass Formula construction uses the Alin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L61-L63

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.Alin_apply (s : Fin r → ℝ) (v : Fin n → ℂ) : Alin ε e f s v = Afun ε e f s v := by sorry
