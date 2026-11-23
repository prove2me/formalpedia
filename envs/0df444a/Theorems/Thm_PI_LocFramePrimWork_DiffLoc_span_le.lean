-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_span_le
-- name    : PI.LocFramePrimWork.DiffLoc_span_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:49.884577+00:00
-- url     : https://prove2.me/theorems/00e19525-5d97-4709-8d8f-93c7bfe25d87
-- title:
--   Loc Frame Prim Work: Diff Loc span le
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L40-L50

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

theorem PI.LocFramePrimWork.DiffLoc_span_le (Q : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E))
    (hQ : ∀ (o : 𝓞 E) (y : Fv F v ⊗[F] E), y ∈ Q → inclR (F := F) (Fv F v) (o : E) * y ∈ Q)
    (T : Set E) (hT : ∀ t ∈ T, inclR (F := F) (Fv F v) t ∈ Q) :
    DiffLoc_psi v (Submodule.span (𝓞 E) T : Set E) ≤ Q := by sorry
