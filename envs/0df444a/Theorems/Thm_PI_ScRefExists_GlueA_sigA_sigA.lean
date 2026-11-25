-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_sigA_sigA
-- name    : PI.ScRefExists.GlueA.sigA_sigA
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:42.748868+00:00
-- url     : https://prove2.me/theorems/8db23c73-a42c-4c85-a111-9b3579f85bd2
-- title:
--   Glue A: sig A sig A
-- statement:
--   The Glue A construction uses the sig A sig A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L35-L43

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

theorem PI.ScRefExists.GlueA.sigA_sigA (x : (I.E ⊗[I.F] Af I.F)) : sigA I (sigA I x) = x := by sorry
