-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lidx_mR
-- name    : PI.IsoDetW.Loc.lidx_mR
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:07:48.400551+00:00
-- url     : https://prove2.me/theorems/1a8b6e2f-bd19-4aaa-8e20-d6e66e73903b
-- title:
--   Loc: lidx m R
-- statement:
--   The Loc construction uses the lidx m R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L31-L34

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

theorem PI.IsoDetW.Loc.lidx_mR (P : HeightOneSpectrum R) {g : Matrix ι ι K} (hg : g.det ≠ 0)
    (A B : Submodule R (ι → K)) :
    lidx P.asIdeal (A.map (mR g)) (B.map (mR g)) = lidx P.asIdeal A B := by sorry
