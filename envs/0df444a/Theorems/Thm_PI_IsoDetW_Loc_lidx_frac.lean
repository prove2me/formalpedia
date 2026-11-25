-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lidx_frac
-- name    : PI.IsoDetW.Loc.lidx_frac
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:07:58.947432+00:00
-- url     : https://prove2.me/theorems/5fedc3c5-72fa-549d-826d-2eb104897419
-- title:
--   Loc: lidx frac
-- statement:
--   The Loc construction uses the lidx frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L179-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L179-L197

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

theorem PI.IsoDetW.Loc.lidx_frac (P : HeightOneSpectrum R) {I J : FI} (hI : I ≠ 0) (hJ : J ≠ 0) :
    lidx P.asIdeal (I : Submodule R K) (J : Submodule R K) =
      FractionalIdeal.count K P J - FractionalIdeal.count K P I := by sorry
