-- Prove2me | Theorems.Thm_PI_WADVR_Sm_mul
-- name    : PI.WADVR.Sm.mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:18.797832+00:00
-- url     : https://prove2.me/theorems/7d9b1661-710d-4ef8-9dc9-2c5e6e9628bd
-- title:
--   Sm: mul
-- statement:
--   The Sm construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L18-L24

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

theorem PI.WADVR.Sm.mul (hϖ : Irreducible ϖ) {k l : ℤ} {a b : Q} (ha : Sm Q ϖ k a) (hb : Sm Q ϖ l b) :
    Sm Q ϖ (k + l) (a * b) := by sorry
