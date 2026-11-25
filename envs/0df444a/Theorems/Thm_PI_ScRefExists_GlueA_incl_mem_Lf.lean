-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_incl_mem_Lf
-- name    : PI.ScRefExists.GlueA.incl_mem_Lf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:22:30.872043+00:00
-- url     : https://prove2.me/theorems/8c517b33-4e17-4a77-ad1f-19abff07d97b
-- title:
--   Glue A: incl mem Lf
-- statement:
--   The Glue A construction uses the incl mem Lf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L149-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L149-L149

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

theorem PI.ScRefExists.GlueA.incl_mem_Lf {x : Fin I.n → I.E} (hx : x ∈ I.L) : incl I x ∈ I.Lf := by sorry
