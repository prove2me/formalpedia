-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_rlen_mulR
-- name    : PI.IsoDetW.Loc.rlen_mulR
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:04.145611+00:00
-- url     : https://prove2.me/theorems/0d403eb9-c185-4304-86d7-d29728b08e9b
-- title:
--   Loc: rlen mul R
-- statement:
--   The Loc construction uses the rlen mul R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L39-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
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
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

theorem PI.IsoDetW.Loc.rlen_mulR (P : HeightOneSpectrum R) {a : K} (ha : a ≠ 0) (I J : FI) :
    relative₂ (localization₂ P.asIdeal ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K))
      (localization₂ P.asIdeal ((FractionalIdeal.spanSingleton _ a * J : FI) : Submodule R K)) =
    relative₂ (localization₂ P.asIdeal (I : Submodule R K)) (localization₂ P.asIdeal (J : Submodule R K)) := by sorry
