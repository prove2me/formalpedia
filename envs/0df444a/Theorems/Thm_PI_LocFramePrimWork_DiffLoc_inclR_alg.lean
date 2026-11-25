-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_inclR_alg
-- name    : PI.LocFramePrimWork.DiffLoc_inclR_alg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:58.323004+00:00
-- url     : https://prove2.me/theorems/513571ed-4ade-4f03-909c-c55119cf81e7
-- title:
--   Loc Frame Prim Work: Diff Loc incl R alg
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc incl R alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L158-L162

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

theorem PI.LocFramePrimWork.DiffLoc_inclR_alg (x : F) :
    inclR (F := F) (Fv F v) (algebraMap F E x) = sc (E := E) v (algebraMap F (Fv F v) x) := by sorry
