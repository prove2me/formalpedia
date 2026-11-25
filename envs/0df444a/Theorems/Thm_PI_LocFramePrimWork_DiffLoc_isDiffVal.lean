-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_isDiffVal
-- name    : PI.LocFramePrimWork.DiffLoc_isDiffVal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:17.950294+00:00
-- url     : https://prove2.me/theorems/f37fad8a-5ac3-4f88-8ee5-bb0e0abf18d3
-- title:
--   Loc Frame Prim Work: Diff Loc is Diff Val
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc is Diff Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L147-L151

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

theorem PI.LocFramePrimWork.DiffLoc_isDiffVal : IsDiffVal v (dV v) := by sorry
