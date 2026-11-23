-- Prove2me | Theorems.Thm_P2M_PI_IsoDetW_Loc_algebraMap_ne_zero__6cbe823fda71
-- name    : P2M_PI_IsoDetW_Loc_algebraMap_ne_zero__6cbe823fda71
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:37:10.504006+00:00
-- url     : https://prove2.me/theorems/43bc8048-da5d-462d-89f8-211802af4088
-- title:
--   P2 M PI Iso Det W Loc algebra Map ne zero  6cbe823fda71: P2 M PI Iso Det W Loc algebra Map ne zero  6cbe823fda71
-- statement:
--   The P2 M PI Iso Det W Loc algebra Map ne zero  6cbe823fda71 construction uses the P2 M PI Iso Det W Loc algebra Map ne zero  6cbe823fda71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L42-L43

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

theorem P2M_PI_IsoDetW_Loc_algebraMap_ne_zero__6cbe823fda71 {r : R} (hr : r ≠ 0) : algebraMap R K r ≠ 0 := by sorry

alias «PI».«IsoDetW».«Loc».«algebraMap_ne_zero'» := P2M_PI_IsoDetW_Loc_algebraMap_ne_zero__6cbe823fda71
