-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_ddE_eq
-- name    : PI.LocFramePrimWork.DiffLoc_ddE_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:11:22.325458+00:00
-- url     : https://prove2.me/theorems/ccaa9c34-049c-41aa-962a-4ea08c88a8f0
-- title:
--   Loc Frame Prim Work: Diff Loc dd E eq
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc dd E eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L164-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L164-L171

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

theorem PI.LocFramePrimWork.DiffLoc_ddE_eq : ((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
    (Submodule.span (𝓞 E) ((fun d : 𝓞 F => algebraMap F E (d : F)) ''
      (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) : Set E) := by sorry
