-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_spanSingleton_mul_le
-- name    : PI.IsoDetW.Loc.spanSingleton_mul_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:18.255579+00:00
-- url     : https://prove2.me/theorems/bba09cc3-0548-5de0-a057-89e450656bd2
-- title:
--   Loc: span Singleton mul le
-- statement:
--   The Loc construction uses the span Singleton mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L169-L173

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

theorem PI.IsoDetW.Loc.spanSingleton_mul_le (x y : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (x * y)) ≤
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) := by sorry
