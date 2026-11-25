-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lidx_mulR
-- name    : PI.IsoDetW.Loc.lidx_mulR
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:16.220572+00:00
-- url     : https://prove2.me/theorems/a329ae63-746c-45d4-8ee8-5ae192ab3ab4
-- title:
--   Loc: lidx mul R
-- statement:
--   The Loc construction uses the lidx mul R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L32-L37

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

theorem PI.IsoDetW.Loc.lidx_mulR (P : HeightOneSpectrum R) {a : K} (ha : a ≠ 0) (I J : FI) :
    lidx P.asIdeal ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K)
      ((FractionalIdeal.spanSingleton _ a * J : FI) : Submodule R K) =
    lidx P.asIdeal (I : Submodule R K) (J : Submodule R K) := by sorry
