-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_chi_diagonal
-- name    : PI.IsoDetW.Loc.chi_diagonal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:21.537219+00:00
-- url     : https://prove2.me/theorems/a3155ffb-3f6c-4328-b29f-7b4ef8fafc56
-- title:
--   Loc: chi diagonal
-- statement:
--   The Loc construction uses the chi diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L178-L184

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

theorem PI.IsoDetW.Loc.chi_diagonal (P : HeightOneSpectrum R) (D : ι → K) (hD : ∀ i, D i ≠ 0) :
    chi R P (Matrix.diagonal D) =
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i)) := by sorry
