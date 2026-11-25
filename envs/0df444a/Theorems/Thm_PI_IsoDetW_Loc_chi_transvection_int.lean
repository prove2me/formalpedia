-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_chi_transvection_int
-- name    : PI.IsoDetW.Loc.chi_transvection_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:14.387009+00:00
-- url     : https://prove2.me/theorems/d13a6889-e004-4d2a-8ee8-e6196ae9e650
-- title:
--   Loc: chi transvection int
-- statement:
--   The Loc construction uses the chi transvection int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L91-L100

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

theorem PI.IsoDetW.Loc.chi_transvection_int (P : HeightOneSpectrum R) {i j : ι} (hij : i ≠ j) (z : R) :
    chi R P (Matrix.transvection i j (algebraMap R K z)) = 0 := by sorry
