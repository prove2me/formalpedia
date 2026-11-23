-- Prove2me | Theorems.Thm_PI_StabBigW_wI_val
-- name    : PI.StabBigW.wI_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:40.710439+00:00
-- url     : https://prove2.me/theorems/9222f9f1-3369-47d7-9071-e2cc832fdc5c
-- title:
--   Stab Big W: w I val
-- statement:
--   The Stab Big W construction uses the w I val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L17-L17

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}

theorem PI.StabBigW.wI_val (t : Fin (k + 1)) : (wI k r t).val = r + t.val := by sorry
