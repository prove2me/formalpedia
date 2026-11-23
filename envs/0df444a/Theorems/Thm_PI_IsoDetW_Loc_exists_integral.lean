-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_exists_integral
-- name    : PI.IsoDetW.Loc.exists_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:50.193665+00:00
-- url     : https://prove2.me/theorems/e7926b63-8ee7-4dea-b2d9-e5871cef88d3
-- title:
--   Loc: exists integral
-- statement:
--   The Loc construction uses the exists integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L53-L64

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

theorem PI.IsoDetW.Loc.exists_integral (I : FI) (hI : I ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ ∃ J : Ideal R, J ≠ 0 ∧
      FractionalIdeal.spanSingleton _ (algebraMap R K a) * I = (J : FI) := by sorry
