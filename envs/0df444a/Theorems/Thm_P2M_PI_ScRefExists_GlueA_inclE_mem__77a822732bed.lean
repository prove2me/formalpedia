-- Prove2me | Theorems.Thm_P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed
-- name    : P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:55:44.673018+00:00
-- url     : https://prove2.me/theorems/b0ec02ac-5ca0-4301-b0f3-bd59001a389e
-- title:
--   P2 M PI Sc Ref Exists Glue A incl E mem  77a822732bed: P2 M PI Sc Ref Exists Glue A incl E mem  77a822732bed
-- statement:
--   The P2 M PI Sc Ref Exists Glue A incl E mem  77a822732bed construction uses the P2 M PI Sc Ref Exists Glue A incl E mem  77a822732bed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L25-L26

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

theorem P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed (t : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E) ∈ IntAf I.F I.E := by sorry

alias «PI».«ScRefExists».«GlueA».«inclE_mem'» := P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed
