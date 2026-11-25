-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_ddE_ne
-- name    : PI.LocFramePrimWork.DiffLoc_ddE_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:11:17.864139+00:00
-- url     : https://prove2.me/theorems/39dbcd04-d493-4d76-a454-c0cd2e684d3a
-- title:
--   Loc Frame Prim Work: Diff Loc dd E ne
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc dd E ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L256-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L256-L259

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

theorem PI.LocFramePrimWork.DiffLoc_ddE_ne : (ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by sorry
