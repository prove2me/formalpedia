-- Prove2me | Theorems.Thm_PI_ScRefExists_Id_intF
-- name    : PI.ScRefExists.Id.intF
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:47.59456+00:00
-- url     : https://prove2.me/theorems/0359d58f-f6bb-4694-8d2f-5cf0f69972a9
-- title:
--   Id: int F
-- statement:
--   The Id construction uses the int F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemTen.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemTen.lean#L23-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemTen
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
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.Id

theorem PI.ScRefExists.Id.intF {F : Type} [Field F] [NumberField F] (r : 𝓞 F) :
    algebraMap F (Af F) (r : F) ∈ Formalism.UG.intAd F := by sorry
