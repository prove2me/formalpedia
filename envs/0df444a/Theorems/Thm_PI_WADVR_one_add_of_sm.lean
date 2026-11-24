-- Prove2me | Theorems.Thm_PI_WADVR_one_add_of_sm
-- name    : PI.WADVR.one_add_of_sm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:29.747099+00:00
-- url     : https://prove2.me/theorems/613ed3de-768f-458c-bad8-a8fccfc32a55
-- title:
--   WADVR: one add of sm
-- statement:
--   The WADVR construction uses the one add of sm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L108-L125

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

theorem PI.WADVR.one_add_of_sm (hϖ : Irreducible ϖ) {t : Q} (ht : Sm Q ϖ 1 t) :
    1 + t ≠ 0 ∧ Sm Q ϖ 0 (1 + t)⁻¹ := by sorry
