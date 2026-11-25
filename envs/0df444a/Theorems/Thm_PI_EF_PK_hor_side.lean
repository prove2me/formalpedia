-- Prove2me | Theorems.Thm_PI_EF_PK_hor_side
-- name    : PI.EF.PK.hor_side
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:31.472055+00:00
-- url     : https://prove2.me/theorems/12267535-4fb0-4e62-aab7-86b4654ba151
-- title:
--   PK: hor side
-- statement:
--   The PK construction uses the hor side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L129-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L129-L141

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

theorem PI.EF.PK.hor_side (G : ℂ → ℂ) (u c T' A h : ℝ) (hu : 1 ≤ u) (hc : -1 / 2 ≤ c) (hT'0 : 0 < T')
    (hA : 0 ≤ A) (hh : |h| = T') (hb : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ c → ‖G ((σ : ℂ) + h * I)‖ ≤ A) :
    ‖∫ x : ℝ in (-1 / 2)..c, G ((x : ℂ) + h * I) * ((u : ℂ) ^ ((x : ℂ) + h * I) / ((x : ℂ) + h * I))‖ ≤
      A * (u ^ c / T') * (c - -1 / 2) := by sorry
