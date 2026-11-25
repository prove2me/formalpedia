-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_std_map_diagonal
-- name    : PI.IsoDetW.Loc.std_map_diagonal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:23.097608+00:00
-- url     : https://prove2.me/theorems/57599e81-42c2-4cc9-acc2-ad427c35027b
-- title:
--   Loc: std map diagonal
-- statement:
--   The Loc construction uses the std map diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L149-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalDet.lean#L149-L164

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

theorem PI.IsoDetW.Loc.std_map_diagonal (D : ι → K) :
    (std : Submodule R (ι → K)).map (mR (Matrix.diagonal D)) =
      Submodule.pi Set.univ (fun i => ((FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i) : FI) :
        Submodule R K)) := by sorry
