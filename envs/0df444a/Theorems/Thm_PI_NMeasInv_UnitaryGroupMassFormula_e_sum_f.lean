-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_e_sum_f
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.e_sum_f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:17:34.879125+00:00
-- url     : https://prove2.me/theorems/10ca9f75-b965-4d5c-84c4-3c93172650ba
-- title:
--   Unitary Group Mass Formula: e sum f
-- statement:
--   The Unitary Group Mass Formula construction uses the e sum f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L91-L93

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.e_sum_f (b : Fin r) (k : Fin r → ℂ) : hJ ε (e b) (∑ c, k c • f c) = k b := by sorry
