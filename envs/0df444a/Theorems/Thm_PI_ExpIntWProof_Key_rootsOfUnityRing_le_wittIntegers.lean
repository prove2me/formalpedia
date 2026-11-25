-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_rootsOfUnityRing_le_wittIntegers
-- name    : PI.ExpIntWProof.Key.rootsOfUnityRing_le_wittIntegers
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:32.531012+00:00
-- url     : https://prove2.me/theorems/be40688b-5189-4efa-b931-4623c9acec82
-- title:
--   Key: roots Of Unity Ring le witt Integers
-- statement:
--   The Key construction uses the roots Of Unity Ring le witt Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L10-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L10-L10

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key

theorem PI.ExpIntWProof.Key.rootsOfUnityRing_le_wittIntegers (p : ℕ) [Fact p.Prime] : S0 p ≤ Wp p := by sorry
