-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_incAdj_inclusion
-- name    : PI.GalTorsConj.W.incAdj_inclusion
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:46.629685+00:00
-- url     : https://prove2.me/theorems/5c46a5a9-c834-4252-bd29-c4a65530ea05
-- title:
--   W: inc Adj inclusion
-- statement:
--   The W construction uses the inc Adj inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/IncAdjInclusion.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/IncAdjInclusion.lean#L17-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Polynomial

theorem PI.GalTorsConj.W.incAdj_inclusion (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁) (x : M) :
    incAdj M M₁ (IntermediateField.inclusion h x) = algebraMap M _ x := by sorry
