-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_rlen_lat_ne_top
-- name    : PI.IsoDetW.Loc.rlen_lat_ne_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:01.377743+00:00
-- url     : https://prove2.me/theorems/49eb75f0-8614-4f77-97e4-bd62ec091123
-- title:
--   Loc: rlen lat ne top
-- statement:
--   The Loc construction uses the rlen lat ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L61-L66

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
omit [DecidableEq ι]

theorem PI.IsoDetW.Loc.rlen_lat_ne_top (P : HeightOneSpectrum R) {A : Submodule R (ι → K)} (hA : IsLat A) {r : R}
    (hr : r ≠ 0) (hrA : sc (algebraMap R K r) ≤ A) :
    relative₂ (localization₂ P.asIdeal (sc (algebraMap R K r))) (localization₂ P.asIdeal A) ≠ ⊤ := by sorry
