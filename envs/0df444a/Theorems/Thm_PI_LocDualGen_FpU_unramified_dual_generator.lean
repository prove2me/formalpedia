-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_unramified_dual_generator
-- name    : PI.LocDualGen.FpU.unramified_dual_generator
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:27:19.310695+00:00
-- url     : https://prove2.me/theorems/d7ab42e1-5191-49aa-90a0-94cde5ba5ef6
-- title:
--   Fp U: unramified dual generator
-- statement:
--   The Fp U construction uses the unramified dual generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean#L158-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean#L158-L206

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
open PI PI.LocDualGen PI.LocDualGen.FpU

theorem PI.LocDualGen.FpU.unramified_dual_generator : PI.LocDualGen.W.FpDualUnram := by sorry
