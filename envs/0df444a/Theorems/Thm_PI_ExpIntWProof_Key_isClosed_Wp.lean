-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_isClosed_Wp
-- name    : PI.ExpIntWProof.Key.isClosed_Wp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:47.54612+00:00
-- url     : https://prove2.me/theorems/e0364ab3-fffb-46a8-9cb0-31296153f91c
-- title:
--   Key: is Closed Wp
-- statement:
--   The Key construction uses the is Closed Wp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L12-L13

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

theorem PI.ExpIntWProof.Key.isClosed_Wp (p : ℕ) [Fact p.Prime] : IsClosed (Wp p : Set ℂ_[p]) := by sorry
