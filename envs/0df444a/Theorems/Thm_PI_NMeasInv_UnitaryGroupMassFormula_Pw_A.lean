-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Pw_A
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.Pw_A
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:12:46.298989+00:00
-- url     : https://prove2.me/theorems/57b6fa7d-c406-4e73-88b4-e4f4ee03e93c
-- title:
--   Unitary Group Mass Formula: Pw A
-- statement:
--   The Unitary Group Mass Formula construction uses the Pw A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L113-L117

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.Pw_A (s : Fin r → ℝ) (v : Fin n → ℂ) : Pw ε e f (Afun ε e f s v) = Pw ε e f v := by sorry
