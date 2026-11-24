-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_Fx_neg
-- name    : PI.ExpIntWProof.Key.Fx.neg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:26.432365+00:00
-- url     : https://prove2.me/theorems/dced6029-fe4b-4bc0-9765-be272c7959a5
-- title:
--   Fx: neg
-- statement:
--   The Fx construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L42-L46

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
variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

theorem PI.ExpIntWProof.Key.Fx.neg {a : R} (ha : Fx p a) : Fx p (-a) := by sorry
