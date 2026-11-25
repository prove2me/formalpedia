-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_rlen_sc_ne_top
-- name    : PI.IsoDetW.Loc.rlen_sc_ne_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:53.70407+00:00
-- url     : https://prove2.me/theorems/49f785f9-a775-4a3d-8047-a2ea3820c0b7
-- title:
--   Loc: rlen sc ne top
-- statement:
--   The Loc construction uses the rlen sc ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L51-L58

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

theorem PI.IsoDetW.Loc.rlen_sc_ne_top (P : HeightOneSpectrum R) {r s : R} (hr : r ≠ 0) (hs : s ≠ 0) :
    relative₂ (localization₂ P.asIdeal (sc (algebraMap R K r) : Submodule R (ι → K)))
      (localization₂ P.asIdeal (sc (algebraMap R K s)⁻¹)) ≠ ⊤ := by sorry
