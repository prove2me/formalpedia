-- Prove2me | Theorems.Thm_PI_LocDualGen_EpC_dichotomy
-- name    : PI.LocDualGen.EpC.dichotomy
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:50.499785+00:00
-- url     : https://prove2.me/theorems/1ceebfde-b9a8-4105-a5aa-6d357e8b8ac9
-- title:
--   Ep C: dichotomy
-- statement:
--   The Ep C construction uses the dichotomy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualCase.lean#L62-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/EpSelfDualCase.lean#L62-L131

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualCase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open PI PI.LocDualGen PI.LocDualGen.EpC
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]

theorem PI.LocDualGen.EpC.dichotomy (hr : finrank K L = 2) (hred : IsReduced L) :
    IsField L ∨ ∃ e : L, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by sorry
