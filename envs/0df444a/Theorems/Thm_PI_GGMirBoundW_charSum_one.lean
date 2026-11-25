-- Prove2me | Theorems.Thm_PI_GGMirBoundW_charSum_one
-- name    : PI.GGMirBoundW.charSum_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:31:10.15272+00:00
-- url     : https://prove2.me/theorems/ede348ac-bcb9-51df-b98f-37ccda43fffa
-- title:
--   GGMir Bound W: char Sum one
-- statement:
--   The GGMir Bound W construction uses the char Sum one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/CharSumOne.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/CharSumOne.lean#L22-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_CharSumOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Finset Matrix
noncomputable section
open Classical

theorem PI.GGMirBoundW.charSum_one {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) (a : F) :
    ∑ t : F, ψ₀ (a * t) = if a = 0 then (Fintype.card F : ℂ) else 0 := by sorry
