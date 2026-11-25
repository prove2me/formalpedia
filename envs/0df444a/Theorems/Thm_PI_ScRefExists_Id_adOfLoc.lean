-- Prove2me | Theorems.Thm_PI_ScRefExists_Id_adOfLoc
-- name    : PI.ScRefExists.Id.adOfLoc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:23:44.34995+00:00
-- url     : https://prove2.me/theorems/989d0960-a758-5be4-ad87-5e5dc6020569
-- title:
--   Id: ad Of Loc
-- statement:
--   The Id construction uses the ad Of Loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L56-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L56-L116

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemAd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.Id

theorem PI.ScRefExists.Id.adOfLoc : AdOfLoc := by sorry
