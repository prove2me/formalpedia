-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_natp_ne_zero
-- name    : PI.ExpIntWProof.Key.natp_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:20.347716+00:00
-- url     : https://prove2.me/theorems/b9a5339b-40c7-4d73-879e-1a4591d78a33
-- title:
--   Key: natp ne zero
-- statement:
--   The Key construction uses the natp ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L104-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L104-L104

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

theorem PI.ExpIntWProof.Key.natp_ne_zero : (p : ℂ_[p]) ≠ 0 := by sorry
