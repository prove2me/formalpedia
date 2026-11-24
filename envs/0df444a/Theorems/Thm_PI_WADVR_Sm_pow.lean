-- Prove2me | Theorems.Thm_PI_WADVR_Sm_pow
-- name    : PI.WADVR.Sm.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:21.67581+00:00
-- url     : https://prove2.me/theorems/14f101c8-7eb7-4f13-bc5d-aec41980edf5
-- title:
--   Sm: pow
-- statement:
--   The Sm construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L53-L61

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

theorem PI.WADVR.Sm.pow (hϖ : Irreducible ϖ) {k : ℤ} {a : Q} (ha : Sm Q ϖ k a) (r : ℕ) :
    Sm Q ϖ (k * r) (a ^ r) := by sorry
