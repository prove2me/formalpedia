-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SchurClosable_Main_schurClosable
-- name    : PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:40.828925+00:00
-- url     : https://prove2.me/theorems/efa3a4a3-becc-4e20-9a06-58d1b4741bf8
-- title:
--   Main: schur Closable
-- statement:
--   The Main construction uses the schur Closable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurUnitaryInner/UnitaryInner.lean#L42-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurUnitaryInner/UnitaryInner.lean#L42-L159

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

theorem PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable : Formalism.IndefR.Leaf.SchurClosable := by sorry
