-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_sc_mono
-- name    : PI.IsoDetW.Loc.sc_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:22.951143+00:00
-- url     : https://prove2.me/theorems/4fca4cda-3fdd-4384-b123-a5c366c8fae6
-- title:
--   Loc: sc mono
-- statement:
--   The Loc construction uses the sc mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/LocalLat.lean#L36-L39

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
omit [IsDedekindDomain R] [DecidableEq ι]

theorem PI.IsoDetW.Loc.sc_mono {a b : K}
    (h : FractionalIdeal.spanSingleton (nonZeroDivisors R) a ≤ FractionalIdeal.spanSingleton (nonZeroDivisors R) b) :
    (sc a : Submodule R (ι → K)) ≤ sc b := by sorry
