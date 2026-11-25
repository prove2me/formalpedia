-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_span_pow
-- name    : PI.LocFramePrimWork.DiffLoc_span_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:13:28.008901+00:00
-- url     : https://prove2.me/theorems/4c13e475-2148-465c-9644-1440dfed2135
-- title:
--   Loc Frame Prim Work: Diff Loc span pow
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc span pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L237-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L237-L242

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

theorem PI.LocFramePrimWork.DiffLoc_span_pow (c : Fv F v ⊗[F] E) (k : ℕ) :
    (Submodule.span (v.adicCompletionIntegers F) {c}) ^ k =
      Submodule.span (v.adicCompletionIntegers F) {c ^ k} := by sorry
