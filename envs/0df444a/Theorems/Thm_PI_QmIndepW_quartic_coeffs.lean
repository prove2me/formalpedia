-- Prove2me | Theorems.Thm_PI_QmIndepW_quartic_coeffs
-- name    : PI.QmIndepW.quartic_coeffs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:08.910425+00:00
-- url     : https://prove2.me/theorems/28db9c41-97e3-5b6f-9376-75477fccf080
-- title:
--   Qm Indep W: quartic coeffs
-- statement:
--   The Qm Indep W construction uses the quartic coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuarticIndependence/IndepC.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuarticIndependence/IndepC.lean#L7-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmIndepW
open Complex

theorem PI.QmIndepW.quartic_coeffs (a0 a1 a2 a3 a4 : ℂ)
    (h : ∀ t : ℕ, 1 ≤ t → t ≤ 5 → a0 + a1 * t + a2 * (t : ℂ) ^ 2 + a3 * (t : ℂ) ^ 3 + a4 * (t : ℂ) ^ 4 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 := by sorry
