-- Prove2me | Theorems.Thm_PI_ScRefExists_Id_mkA_apply
-- name    : PI.ScRefExists.Id.mkA_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:44.83548+00:00
-- url     : https://prove2.me/theorems/229e3b7c-452e-48c5-a27a-1600f24da68c
-- title:
--   Id: mk A apply
-- statement:
--   The Id construction uses the mk A apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L40-L41

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

theorem PI.ScRefExists.Id.mkA_apply (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, Valued.v (c v) ≤ 1) (v : HeightOneSpectrum (𝓞 F)) : mkA c hc v = c v := by sorry
