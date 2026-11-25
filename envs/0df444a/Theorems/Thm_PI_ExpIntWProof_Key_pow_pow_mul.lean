-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_pow_pow_mul
-- name    : PI.ExpIntWProof.Key.pow_pow_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:32.309609+00:00
-- url     : https://prove2.me/theorems/77648490-0bc3-4254-a6a1-e0370c25a1a7
-- title:
--   Key: pow pow mul
-- statement:
--   The Key construction uses the pow pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L15-L19

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

theorem PI.ExpIntWProof.Key.pow_pow_mul {R : Type*} [CommRing R] (a : R) (p f : ℕ) (h : a ^ p ^ f = a) :
    ∀ k : ℕ, a ^ p ^ (f * k) = a
  := by sorry
