-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_spanLt
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.A_spanLt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:58.28428+00:00
-- url     : https://prove2.me/theorems/39b51ea1-e69a-5b23-be95-f8c797b206d1
-- title:
--   Unitary Group Mass Formula: A span Lt
-- statement:
--   The Unitary Group Mass Formula construction uses the A span Lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L145-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L145-L158

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.A_spanLt (s : Fin r → ℝ) (k : ℕ) {v : Fin n → ℂ} (hv : v ∈ spanLt e k) :
    Afun ε e f s v ∈ spanLt e k := by sorry
