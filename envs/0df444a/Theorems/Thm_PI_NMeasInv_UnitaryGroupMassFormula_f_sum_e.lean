-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_f_sum_e
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.f_sum_e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:27:48.607782+00:00
-- url     : https://prove2.me/theorems/07ae7c37-c5c9-4eff-a29b-a60ab8224b61
-- title:
--   Unitary Group Mass Formula: f sum e
-- statement:
--   The Unitary Group Mass Formula construction uses the f sum e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L79-L81

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.f_sum_e (b : Fin r) (k : Fin r → ℂ) : hJ ε (f b) (∑ c, k c • e c) = k b := by sorry
