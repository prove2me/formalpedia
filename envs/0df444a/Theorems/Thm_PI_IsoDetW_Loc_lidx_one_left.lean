-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_lidx_one_left
-- name    : PI.IsoDetW.Loc.lidx_one_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:08.463457+00:00
-- url     : https://prove2.me/theorems/c86d46ae-1597-5b07-815d-bb77bfa5b409
-- title:
--   Loc: lidx one left
-- statement:
--   The Loc construction uses the lidx one left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L110-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L110-L139

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

theorem PI.IsoDetW.Loc.lidx_one_left (P : HeightOneSpectrum R) {I : FI} (hI : I ≠ 0) :
    lidx P.asIdeal (1 : Submodule R K) (I : Submodule R K) = FractionalIdeal.count K P I := by sorry
