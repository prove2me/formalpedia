-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_chi_mul
-- name    : PI.IsoDetW.Loc.chi_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:41.992729+00:00
-- url     : https://prove2.me/theorems/2f9e6692-ec4c-4c58-b7db-bb70545090d5
-- title:
--   Loc: chi mul
-- statement:
--   The Loc construction uses the chi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L64-L69

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

theorem PI.IsoDetW.Loc.chi_mul (P : HeightOneSpectrum R) {g h : Matrix ι ι K} (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    chi R P (g * h) = chi R P g + chi R P h := by sorry
