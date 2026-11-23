-- Prove2me | Theorems.Thm_PI_Tr_keySmall
-- name    : PI.Tr.keySmall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:08.579225+00:00
-- url     : https://prove2.me/theorems/451cec24-565f-4031-b0d3-84ebe46aab57
-- title:
--   Tr: key Small
-- statement:
--   The Tr construction uses the key Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/KeySmall.lean#L25-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/KeySmall.lean#L25-L74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_KeySmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open PI PI.Tr

theorem PI.Tr.keySmall : KeySmall := by sorry
