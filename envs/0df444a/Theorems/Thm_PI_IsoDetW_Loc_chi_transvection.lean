-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_chi_transvection
-- name    : PI.IsoDetW.Loc.chi_transvection
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:26.244069+00:00
-- url     : https://prove2.me/theorems/bc5adaab-6d7b-42be-8bbc-6431164e1b10
-- title:
--   Loc: chi transvection
-- statement:
--   The Loc construction uses the chi transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L102-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L102-L147

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

theorem PI.IsoDetW.Loc.chi_transvection (P : HeightOneSpectrum R) {i j : ι} (hij : i ≠ j) (c : K) :
    chi R P (Matrix.transvection i j c) = 0 := by sorry
