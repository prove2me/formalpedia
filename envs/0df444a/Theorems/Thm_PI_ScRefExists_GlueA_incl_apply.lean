-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_incl_apply
-- name    : PI.ScRefExists.GlueA.incl_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:10.250806+00:00
-- url     : https://prove2.me/theorems/d62e72cf-01ed-54d8-a7db-8c67c2e15d7c
-- title:
--   Glue A: incl apply
-- statement:
--   The Glue A construction uses the incl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L112-L113

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

theorem PI.ScRefExists.GlueA.incl_apply (x : Fin I.n → I.E) (i : Fin I.n) :
    incl I x i = Formalism.UG.inclE (F := I.F) (Af I.F) (x i) := by sorry
