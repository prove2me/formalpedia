-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_root_frob
-- name    : PI.ExpIntWProof.Key.root_frob
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:45.808428+00:00
-- url     : https://prove2.me/theorems/903d684e-1dd9-475f-a2f2-b9fda4974f6e
-- title:
--   Key: root frob
-- statement:
--   The Key construction uses the root frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L52-L58

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
variable {p : ℕ} [hp : Fact p.Prime]

theorem PI.ExpIntWProof.Key.root_frob {x : ℂ_[p]} {n : ℕ} (_hn : 0 < n) (hc : Nat.Coprime n p) (hx : x ^ n = 1) :
    x ^ p ^ Nat.totient n = x := by sorry
