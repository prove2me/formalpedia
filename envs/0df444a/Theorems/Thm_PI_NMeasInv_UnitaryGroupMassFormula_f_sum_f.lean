-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_f_sum_f
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.f_sum_f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:50.641768+00:00
-- url     : https://prove2.me/theorems/55e24aad-aa27-4f1e-ac29-5365e669b3ae
-- title:
--   Unitary Group Mass Formula: f sum f
-- statement:
--   The Unitary Group Mass Formula construction uses the f sum f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L83-L85

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.f_sum_f (b : Fin r) (k : Fin r → ℂ) : hJ ε (f b) (∑ c, k c • f c) = 0 := by sorry
