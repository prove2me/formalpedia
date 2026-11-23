-- Prove2me | Theorems.Thm_P2M_PI_IsoDetW_Loc_spanSingleton_ne_zero__2b9a00487365
-- name    : P2M_PI_IsoDetW_Loc_spanSingleton_ne_zero__2b9a00487365
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:49.166922+00:00
-- url     : https://prove2.me/theorems/7efa6e28-4a09-4f5b-ba58-bfd5def093ef
-- title:
--   P2 M PI Iso Det W Loc span Singleton ne zero  2b9a00487365: P2 M PI Iso Det W Loc span Singleton ne zero  2b9a00487365
-- statement:
--   The P2 M PI Iso Det W Loc span Singleton ne zero  2b9a00487365 construction uses the P2 M PI Iso Det W Loc span Singleton ne zero  2b9a00487365 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L46-L48

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

theorem P2M_PI_IsoDetW_Loc_spanSingleton_ne_zero__2b9a00487365 {a : K} (ha : a ≠ 0) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≠ 0 := by sorry

alias «PI».«IsoDetW».«Loc».«spanSingleton_ne_zero'» := P2M_PI_IsoDetW_Loc_spanSingleton_ne_zero__2b9a00487365
