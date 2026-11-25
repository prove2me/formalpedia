-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_rlen_ne_top
-- name    : PI.IsoDetW.Loc.rlen_ne_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:11.373384+00:00
-- url     : https://prove2.me/theorems/7c679619-da34-42f2-b0be-fa7421519028
-- title:
--   Loc: rlen ne top
-- statement:
--   The Loc construction uses the rlen ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L69-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/SpanSingletonAlgebraMap.lean#L69-L94

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

theorem PI.IsoDetW.Loc.rlen_ne_top (P : HeightOneSpectrum R) {D X : FI} (hD : D ≠ 0) (hDX : D ≤ X) :
    relative₂ (localization₂ P.asIdeal (D : Submodule R K)) (localization₂ P.asIdeal (X : Submodule R K)) ≠ ⊤ := by sorry
