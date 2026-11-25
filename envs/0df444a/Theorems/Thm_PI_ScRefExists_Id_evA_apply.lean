-- Prove2me | Theorems.Thm_PI_ScRefExists_Id_evA_apply
-- name    : PI.ScRefExists.Id.evA_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:23:56.613068+00:00
-- url     : https://prove2.me/theorems/56087873-f2bd-5391-a919-b284c4cd9d8b
-- title:
--   Id: ev A apply
-- statement:
--   The Id construction uses the ev A apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L28-L28

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
variable {F : Type} [Field F] [NumberField F]

theorem PI.ScRefExists.Id.evA_apply (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evA v a = a v := by sorry
