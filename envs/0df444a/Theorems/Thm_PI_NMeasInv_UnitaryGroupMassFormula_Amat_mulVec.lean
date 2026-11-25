-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Amat_mulVec
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.Amat_mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:35.934258+00:00
-- url     : https://prove2.me/theorems/ee0193c5-0c84-561e-9ed1-edab086b8fa2
-- title:
--   Unitary Group Mass Formula: Amat mul Vec
-- statement:
--   The Unitary Group Mass Formula construction uses the Amat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L68-L70

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.Amat_mulVec (s : Fin r → ℝ) (v : Fin n → ℂ) : Amat ε e f s *ᵥ v = Afun ε e f s v := by sorry
