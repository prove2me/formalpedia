-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_inclE_tmul
-- name    : PI.ScRefExists.GlueA.inclE_tmul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:06.469997+00:00
-- url     : https://prove2.me/theorems/7cd3cf30-dd45-4ad9-964f-32bd2914124c
-- title:
--   Glue A: incl E tmul
-- statement:
--   The Glue A construction uses the incl E tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L13-L13

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

theorem PI.ScRefExists.GlueA.inclE_tmul (a : I.E) : Formalism.UG.inclE (F := I.F) (Af I.F) a = a ⊗ₜ[I.F] (1 : Af I.F) := by sorry
