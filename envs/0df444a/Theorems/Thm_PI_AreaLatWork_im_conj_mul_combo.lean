-- Prove2me | Theorems.Thm_PI_AreaLatWork_im_conj_mul_combo
-- name    : PI.AreaLatWork.im_conj_mul_combo
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:26.309483+00:00
-- url     : https://prove2.me/theorems/8993d40d-a6f9-4b2d-9fc8-065a4995d856
-- title:
--   Area Lat Work: im conj mul combo
-- statement:
--   The Area Lat Work construction uses the im conj mul combo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeArea/ImConjMulCombo.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeArea/ImConjMulCombo.lean#L8-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeArea_ImConjMulCombo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AreaLatWork
open PI

theorem PI.AreaLatWork.im_conj_mul_combo (w₁ w₂ : ℂ) (m n m' n' : ℤ) :
    ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im
      = ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by sorry
