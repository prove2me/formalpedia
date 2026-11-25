-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_chi_eq
-- name    : PI.IsoDetW.Loc.chi_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:46:27.652304+00:00
-- url     : https://prove2.me/theorems/38c216c8-7804-4a46-a173-ba9b5292bbde
-- title:
--   Loc: chi eq
-- statement:
--   The Loc construction uses the chi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L186-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L186-L203

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

theorem PI.IsoDetW.Loc.chi_eq (P : HeightOneSpectrum R) (g : Matrix ι ι K) (hg : g.det ≠ 0) :
    chi R P g = FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) g.det) := by sorry
