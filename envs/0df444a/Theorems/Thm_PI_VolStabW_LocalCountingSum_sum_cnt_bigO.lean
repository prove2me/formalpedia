-- Prove2me | Theorems.Thm_PI_VolStabW_LocalCountingSum_sum_cnt_bigO
-- name    : PI.VolStabW.LocalCountingSum.sum_cnt_bigO
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:16.970801+00:00
-- url     : https://prove2.me/theorems/77df85f7-cb34-449d-a919-7f99ca6ed6b2
-- title:
--   Local Counting Sum: sum cnt big O
-- statement:
--   The Local Counting Sum construction uses the sum cnt big O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensQ.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensQ.lean#L31-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors
open PI.VolStabW.LocalCountingSum
variable (K : Type) [Field K] [NumberField K]

theorem PI.VolStabW.LocalCountingSum.sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by sorry
