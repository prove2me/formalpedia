-- Prove2me | Theorems.Thm_PI_EF_PK_vert_cancel
-- name    : PI.EF.PK.vert_cancel
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:03.687804+00:00
-- url     : https://prove2.me/theorems/d0c4ad88-58aa-4f02-aab9-c4eb2f04c15c
-- title:
--   PK: vert cancel
-- statement:
--   The PK construction uses the vert cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L159-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L159-L167

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

theorem PI.EF.PK.vert_cancel (G k : ℝ → ℂ) (T' : ℝ) :
    2 * π * I * ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in -T'..T', -G t * k t) =
      -(I * ∫ t : ℝ in -T'..T', G t * k t) := by sorry
