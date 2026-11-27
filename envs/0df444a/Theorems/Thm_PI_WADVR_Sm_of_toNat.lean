-- Prove2me | Theorems.Thm_PI_WADVR_Sm_of_toNat
-- name    : PI.WADVR.Sm.of_toNat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:01.07443+00:00
-- url     : https://prove2.me/theorems/ed18be08-38f3-40a0-8b59-1e9b4c8eaa30
-- title:
--   Sm: of to Nat
-- statement:
--   The Sm construction uses the of to Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L170-L172

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

theorem PI.WADVR.Sm.of_toNat (hϖ : Irreducible ϖ) {k : ℤ} {a : Q} (ha : Sm Q ϖ (k.toNat : ℤ) a) :
    Sm Q ϖ k a := by sorry
