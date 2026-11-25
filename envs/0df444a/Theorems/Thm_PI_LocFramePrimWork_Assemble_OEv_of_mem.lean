-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_OEv_of_mem
-- name    : PI.LocFramePrimWork.Assemble_OEv_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:09.695026+00:00
-- url     : https://prove2.me/theorems/08a57d9b-5b75-50c6-bce8-df0b49549474
-- title:
--   Loc Frame Prim Work: Assemble OEv of mem
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble OEv of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L63-L70

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem PI.LocFramePrimWork.Assemble_OEv_of_mem (y : Fv F v ⊗[F] E)
    (hy : y ∈ Submodule.span (v.adicCompletionIntegers F)
      (inclR (F := F) (Fv F v) '' Set.range ((↑) : 𝓞 E → E))) : y ∈ OEv (E := E) v := by sorry
