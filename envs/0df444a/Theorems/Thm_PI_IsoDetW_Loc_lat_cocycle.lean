-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lat_cocycle
-- name    : PI.IsoDetW.Loc.lat_cocycle
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:08.063402+00:00
-- url     : https://prove2.me/theorems/3d585811-af11-4a52-932a-2815f69cb55a
-- title:
--   Loc: lat cocycle
-- statement:
--   The Loc construction uses the lat cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L69-L82

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

theorem PI.IsoDetW.Loc.lat_cocycle (P : HeightOneSpectrum R) {A B C : Submodule R (ι → K)} (hA : IsLat A) (hB : IsLat B)
    (hC : IsLat C) : lidx P.asIdeal A C = lidx P.asIdeal A B + lidx P.asIdeal B C := by sorry
