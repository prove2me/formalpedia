-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_map_sc_le
-- name    : PI.IsoDetW.Loc.map_sc_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:17.30942+00:00
-- url     : https://prove2.me/theorems/e19bb54a-7286-5b16-a5b0-290671cdefbc
-- title:
--   Loc: map sc le
-- statement:
--   The Loc construction uses the map sc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L101-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L101-L116

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

theorem PI.IsoDetW.Loc.map_sc_le (M : Matrix ι ι K) {d : R} (hd0 : d ≠ 0)
    (hd : ∀ i j, IsLocalization.IsInteger R (d • M i j)) (a : K) :
    (sc a : Submodule R (ι → K)).map (M.mulVecLin.restrictScalars R) ≤ sc (a * (algebraMap R K d)⁻¹) := by sorry
