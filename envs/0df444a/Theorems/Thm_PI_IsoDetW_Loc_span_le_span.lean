-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_span_le_span
-- name    : PI.IsoDetW.Loc.span_le_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:37:11.868887+00:00
-- url     : https://prove2.me/theorems/1606bbe2-02a9-41f6-999f-e65562ca9fb0
-- title:
--   Loc: span le span
-- statement:
--   The Loc construction uses the span le span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L30-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
omit [IsDedekindDomain R]

theorem PI.IsoDetW.Loc.span_le_span {a b : K} (t : R) (h : a = algebraMap R K t * b) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ FractionalIdeal.spanSingleton (nonZeroDivisors R) b := by sorry
