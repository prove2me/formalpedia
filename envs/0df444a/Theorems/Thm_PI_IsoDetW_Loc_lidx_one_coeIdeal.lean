-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lidx_one_coeIdeal
-- name    : PI.IsoDetW.Loc.lidx_one_coeIdeal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:02.545654+00:00
-- url     : https://prove2.me/theorems/772ccc15-182c-5cd7-a749-10f06e515872
-- title:
--   Loc: lidx one coe Ideal
-- statement:
--   The Loc construction uses the lidx one coe Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L96-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L96-L104

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

theorem PI.IsoDetW.Loc.lidx_one_coeIdeal (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    lidx P.asIdeal (1 : Submodule R K) ((J : FI) : Submodule R K) = FractionalIdeal.count K P (J : FI) := by sorry
