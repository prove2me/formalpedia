-- Prove2me | Theorems.Thm_PI_WADVR_big_of_not_mem
-- name    : PI.WADVR.big_of_not_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:43:55.294467+00:00
-- url     : https://prove2.me/theorems/c0063455-33f7-402e-90df-03b5509e4e3c
-- title:
--   WADVR: big of not mem
-- statement:
--   The WADVR construction uses the big of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L79-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L79-L93

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

theorem PI.WADVR.big_of_not_mem (hϖ : Irreducible ϖ) {q : Q} (hq : q ∉ Set.range (algebraMap W Q)) :
    q ≠ 0 ∧ Sm Q ϖ 1 q⁻¹ := by sorry
