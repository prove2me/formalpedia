-- Prove2me | Theorems.Thm_PI_WADVR_Sm_add
-- name    : PI.WADVR.Sm.add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:38.262433+00:00
-- url     : https://prove2.me/theorems/0a0845af-7359-4cf0-8ba9-736186c41fc0
-- title:
--   Sm: add
-- statement:
--   The Sm construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L26-L29

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

theorem PI.WADVR.Sm.add {k : ℤ} {a b : Q} (ha : Sm Q ϖ k a) (hb : Sm Q ϖ k b) : Sm Q ϖ k (a + b) := by sorry
