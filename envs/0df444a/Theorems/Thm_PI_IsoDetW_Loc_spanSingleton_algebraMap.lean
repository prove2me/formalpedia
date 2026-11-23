-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_spanSingleton_algebraMap
-- name    : PI.IsoDetW.Loc.spanSingleton_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:30.834808+00:00
-- url     : https://prove2.me/theorems/6280910e-4df4-4194-b426-90ee4f50f012
-- title:
--   Loc: span Singleton algebra Map
-- statement:
--   The Loc construction uses the span Singleton algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L106-L108

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

theorem PI.IsoDetW.Loc.spanSingleton_algebraMap (a : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) = ((Ideal.span {a} : Ideal R) : FI) := by sorry
