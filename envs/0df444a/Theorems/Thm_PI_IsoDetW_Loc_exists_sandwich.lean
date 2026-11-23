-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_exists_sandwich
-- name    : PI.IsoDetW.Loc.exists_sandwich
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:40.679821+00:00
-- url     : https://prove2.me/theorems/51ed3a8e-9490-4ad3-8135-9a7feacc7f45
-- title:
--   Loc: exists sandwich
-- statement:
--   The Loc construction uses the exists sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L141-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L141-L167

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

theorem PI.IsoDetW.Loc.exists_sandwich (I : FI) (hI : I ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ FractionalIdeal.spanSingleton _ (algebraMap R K r) ≤ I ∧
      I ≤ FractionalIdeal.spanSingleton _ (algebraMap R K r)⁻¹ := by sorry
