-- Prove2me | Theorems.Thm_PI_EF_PK_left_side
-- name    : PI.EF.PK.left_side
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:51.767858+00:00
-- url     : https://prove2.me/theorems/b74891fd-3dfb-4020-93fd-2b7681a5dac7
-- title:
--   PK: left side
-- statement:
--   The PK construction uses the left side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L143-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L143-L157

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

theorem PI.EF.PK.left_side (G : ℂ → ℂ) (u T' K2 : ℝ) (hu : 1 ≤ u) (hT'0 : 0 < T') (hK20 : 0 ≤ K2)
    (hb : ∀ t : ℝ, |t| ≤ T' → ‖G (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K2) :
    ‖∫ t : ℝ in -T'..T', G (((-1 / 2 : ℝ) : ℂ) + t * I) *
        ((u : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I) / (((-1 / 2 : ℝ) : ℂ) + t * I))‖ ≤
      K2 * (2 * Real.arsinh (2 * T')) := by sorry
