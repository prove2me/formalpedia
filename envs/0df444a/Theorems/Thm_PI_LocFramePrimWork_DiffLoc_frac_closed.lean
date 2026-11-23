-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_frac_closed
-- name    : PI.LocFramePrimWork.DiffLoc_frac_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:38.337516+00:00
-- url     : https://prove2.me/theorems/451b5fd7-9847-4b37-bfcd-101ea118b533
-- title:
--   Loc Frame Prim Work: Diff Loc frac closed
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc frac closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L52-L56

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

theorem PI.LocFramePrimWork.DiffLoc_frac_closed (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    ∀ (o : 𝓞 E) (s : E), s ∈ (I : Set E) → (o : E) * s ∈ (I : Set E) := by sorry
