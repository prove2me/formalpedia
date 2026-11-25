-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_hJ_sub
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.hJ_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:13:35.780863+00:00
-- url     : https://prove2.me/theorems/9095287a-a074-56cd-9b40-5800f4ca4934
-- title:
--   Unitary Group Mass Formula: h J sub
-- statement:
--   The Unitary Group Mass Formula construction uses the h J sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L20-L21

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.hJ_sub (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by sorry
