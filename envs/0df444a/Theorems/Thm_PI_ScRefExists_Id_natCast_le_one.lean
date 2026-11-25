-- Prove2me | Theorems.Thm_PI_ScRefExists_Id_natCast_le_one
-- name    : PI.ScRefExists.Id.natCast_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:39:20.491272+00:00
-- url     : https://prove2.me/theorems/86ea549f-8e2b-4984-ab41-01d7c78c36e0
-- title:
--   Id: nat Cast le one
-- statement:
--   The Id construction uses the nat Cast le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemAd.lean#L51-L52

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

theorem PI.ScRefExists.Id.natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) :
    Valued.v ((g : ℕ) : v.adicCompletion F) ≤ 1 := by sorry
