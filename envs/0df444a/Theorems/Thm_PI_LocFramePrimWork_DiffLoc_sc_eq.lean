-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_DiffLoc_sc_eq
-- name    : PI.LocFramePrimWork.DiffLoc_sc_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:16:15.365412+00:00
-- url     : https://prove2.me/theorems/930bf40f-f023-454b-b0a1-908a8bb2f329
-- title:
--   Loc Frame Prim Work: Diff Loc sc eq
-- statement:
--   The Loc Frame Prim Work construction uses the Diff Loc sc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L153-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DiffLoc.lean#L153-L153

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

theorem PI.LocFramePrimWork.DiffLoc_sc_eq (x : Fv F v) : sc (E := E) v x = algebraMap (Fv F v) (Fv F v ⊗[F] E) x := by sorry
