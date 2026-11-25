-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SchurClosable_Main_unitary_inner
-- name    : PI.UnitaryGroupMassFormula.SchurClosable.Main.unitary_inner
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:09.075276+00:00
-- url     : https://prove2.me/theorems/2457f90f-0b82-4558-89b2-459cb228f0b4
-- title:
--   Main: unitary inner
-- statement:
--   The Main construction uses the unitary inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurUnitaryInner/UnitaryInner.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurUnitaryInner/UnitaryInner.lean#L8-L10

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurUnitaryInner_UnitaryInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SchurClosable PI.UnitaryGroupMassFormula.SchurClosable.Main
open Filter Topology

theorem PI.UnitaryGroupMassFormula.SchurClosable.Main.unitary_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (hT : ∀ x, ‖T x‖ = ‖x‖) (x y : H) : inner ℂ (T x) (T y) = inner ℂ x y := by sorry
