-- Prove2me | Theorems.Thm_PI_StabBigW_ut_of_mem
-- name    : PI.StabBigW.ut_of_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:26.218486+00:00
-- url     : https://prove2.me/theorems/96cc02ff-2ecf-57dc-8feb-2b239a05b9fb
-- title:
--   Stab Big W: ut of mem
-- statement:
--   The Stab Big W construction uses the ut of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L99-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L99-L172

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

theorem PI.StabBigW.ut_of_mem {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : UT k r a := by sorry
