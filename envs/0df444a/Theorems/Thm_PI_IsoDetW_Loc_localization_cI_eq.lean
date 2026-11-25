-- Prove2me | Theorems.Thm_PI_IsoDetW_Loc_localization_cI_eq
-- name    : PI.IsoDetW.Loc.localization_cI_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:26.054806+00:00
-- url     : https://prove2.me/theorems/7009044d-99f8-43ae-8bb1-b5e877489da5
-- title:
--   Loc: localization c I eq
-- statement:
--   The Loc construction uses the localization c I eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean#L102-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDeterminant/AlgebraMapMemCI.lean#L102-L144

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
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

theorem PI.IsoDetW.Loc.localization_cI_eq (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    localization₂ P.asIdeal (cI K J) =
      localization₂ P.asIdeal (cI K (P.asIdeal ^ (Associates.mk P.asIdeal).count (Associates.mk J).factors)) := by sorry
