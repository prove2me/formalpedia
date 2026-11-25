-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_range_closed
-- name    : PI.LocFramePrimWork.DiffLoc_range_closed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:12:56.667012+00:00
-- url     : https://prove2.me/theorems/b743ae23-7ed0-5c8f-8388-5ed3db3ab8a3
-- title:
--   Loc Frame Prim Work: Diff Loc range closed
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc range closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L58-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
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
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.LocFramePrimWork.DiffLoc_range_closed :
    ∀ (o : 𝓞 E) (s : E), s ∈ Set.range ((↑) : 𝓞 E → E) → (o : E) * s ∈ Set.range ((↑) : 𝓞 E → E) := by sorry
