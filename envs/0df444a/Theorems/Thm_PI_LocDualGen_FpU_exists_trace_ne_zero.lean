-- Prove2me | Theorems.Thm_PI_LocDualGen_FpU_exists_trace_ne_zero
-- name    : PI.LocDualGen.FpU.exists_trace_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:16.55136+00:00
-- url     : https://prove2.me/theorems/47f2f671-b54d-446f-aa41-46d2d8693c7a
-- title:
--   Fp U: exists trace ne zero
-- statement:
--   The Fp U construction uses the exists trace ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/UnramifiedDualGenerator.lean#L12-L17

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

theorem PI.LocDualGen.FpU.exists_trace_ne_zero (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [Algebra (ZMod p) F] : ∃ z : F, Algebra.trace (ZMod p) F z ≠ 0 := by sorry
