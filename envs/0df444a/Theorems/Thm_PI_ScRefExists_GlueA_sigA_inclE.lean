-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_sigA_inclE
-- name    : PI.ScRefExists.GlueA.sigA_inclE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:31.084172+00:00
-- url     : https://prove2.me/theorems/6c7b7ab4-ca5e-4fe3-a9c0-3f16802feda7
-- title:
--   Glue A: sig A incl E
-- statement:
--   The Glue A construction uses the sig A incl E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L28-L33

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

theorem PI.ScRefExists.GlueA.sigA_inclE (a : I.E) :
    sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) = Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by sorry
