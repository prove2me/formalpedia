-- Prove2me | Theorems.Thm_PI_EF_PK_seg_bound
-- name    : PI.EF.PK.seg_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:05.867875+00:00
-- url     : https://prove2.me/theorems/2a13df09-423e-48b6-b089-acbac50ef79f
-- title:
--   PK: seg bound
-- statement:
--   The PK construction uses the seg bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L8-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real

theorem PI.EF.PK.seg_bound (f : ℝ → ℂ) (K a b : ℝ) (hab : a ≤ b) (h : ∀ x, a ≤ x → x ≤ b → ‖f x‖ ≤ K) :
    ‖∫ x in a..b, f x‖ ≤ K * (b - a) := by sorry
