-- Prove2me | Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_f_A
-- name    : PI.NMeasInv.UnitaryGroupMassFormula.f_A
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:17:22.2146+00:00
-- url     : https://prove2.me/theorems/7d3ed262-39de-4561-82bd-ca263e7bcb27
-- title:
--   Unitary Group Mass Formula: f A
-- statement:
--   The Unitary Group Mass Formula construction uses the f A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/AmatInvMul.lean#L103-L106

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

theorem PI.NMeasInv.UnitaryGroupMassFormula.f_A (s : Fin r → ℝ) (b : Fin r) (v : Fin n → ℂ) :
    hJ ε (f b) (Afun ε e f s v) = (s b : ℂ) * hJ ε (f b) v := by sorry
