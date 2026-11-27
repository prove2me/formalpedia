-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_hA_Lf
-- name    : PI.ScRefExists.GlueA.hA_Lf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:52:57.339382+00:00
-- url     : https://prove2.me/theorems/b2b156ef-31e3-5d9d-bc5e-7fe6acc6eead
-- title:
--   Glue A: h A Lf
-- statement:
--   The Glue A construction uses the h A Lf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L156-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L156-L182

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

theorem PI.ScRefExists.GlueA.hA_Lf {x y : VA I} (hx : x ∈ I.Lf) (hy : y ∈ I.Lf) : hA I x y ∈ IntAf I.F I.E := by sorry
