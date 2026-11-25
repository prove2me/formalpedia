-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_nondeg
-- name    : PI.SelfDualLoc.W.nondeg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:18.71026+00:00
-- url     : https://prove2.me/theorems/677a5840-0400-4567-8786-422c7710245d
-- title:
--   W: nondeg
-- statement:
--   The W construction uses the nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/Nondeg.lean#L83-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/Nondeg.lean#L83-L103

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc ND

theorem PI.SelfDualLoc.W.nondeg : Nondeg := by sorry
