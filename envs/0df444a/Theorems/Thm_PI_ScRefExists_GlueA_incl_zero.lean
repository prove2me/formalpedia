-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_incl_zero
-- name    : PI.ScRefExists.GlueA.incl_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:44.663471+00:00
-- url     : https://prove2.me/theorems/a8af8d09-957c-5ec8-8869-e98b0876895e
-- title:
--   Glue A: incl zero
-- statement:
--   The Glue A construction uses the incl zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L127-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.GlueA.incl_zero : incl I 0 = 0 := by sorry
