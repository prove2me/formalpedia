-- Prove2me | Theorems.Thm_PI_WADVR_sm_one_of_mem
-- name    : PI.WADVR.sm_one_of_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:43:21.589171+00:00
-- url     : https://prove2.me/theorems/e816e579-9bc8-44ac-9b10-92a83093ef49
-- title:
--   WADVR: sm one of mem
-- statement:
--   The WADVR construction uses the sm one of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L68-L73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
variable {ϖ : W}

theorem PI.WADVR.sm_one_of_mem (hϖ : Irreducible ϖ) {w : W} (hw : w ∈ IsLocalRing.maximalIdeal W) :
    Sm Q ϖ 1 (algebraMap W Q w) := by sorry
