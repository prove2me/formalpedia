-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_star_int
-- name    : PI.ScRefExists.GlueA.star_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:03.528613+00:00
-- url     : https://prove2.me/theorems/e6fb0ea0-aa90-42b6-9774-32ec88d33de6
-- title:
--   Glue A: star int
-- statement:
--   The Glue A construction uses the star int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L15-L18

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

theorem PI.ScRefExists.GlueA.star_int (t : 𝓞 I.E) : star (t : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := by sorry
