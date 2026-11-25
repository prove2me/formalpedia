-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_mR_sat
-- name    : PI.IsoDetW.Loc.mR_sat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:36.591892+00:00
-- url     : https://prove2.me/theorems/35aa2d33-7924-53d0-9e9a-1b54386d3189
-- title:
--   Loc: m R sat
-- statement:
--   The Loc construction uses the m R sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L26-L29

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

theorem PI.IsoDetW.Loc.mR_sat (P : HeightOneSpectrum R) (g : Matrix ι ι K) (s : R) (y : ι → K)
    (hs : s ∈ P.asIdeal.primeCompl) (hy : s • y ∈ LinearMap.range (mR (R := R) g)) :
    y ∈ LinearMap.range (mR (R := R) g) := by sorry
