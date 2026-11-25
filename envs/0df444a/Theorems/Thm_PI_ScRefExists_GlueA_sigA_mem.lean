-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_sigA_mem
-- name    : PI.ScRefExists.GlueA.sigA_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:56:10.678084+00:00
-- url     : https://prove2.me/theorems/68b802c7-cac7-47d3-9718-05e8cdd3463b
-- title:
--   Glue A: sig A mem
-- statement:
--   The Glue A construction uses the sig A mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L45-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L45-L65

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

theorem PI.ScRefExists.GlueA.sigA_mem {x : (I.E ⊗[I.F] Af I.F)} (hx : x ∈ IntAf I.F I.E) : sigA I x ∈ IntAf I.F I.E := by sorry
