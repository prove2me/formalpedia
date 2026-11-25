-- Prove2me | Theorems.Thm_PI_VolStabW_LocalCountingSum_sum_cnt
-- name    : PI.VolStabW.LocalCountingSum.sum_cnt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:40:18.680488+00:00
-- url     : https://prove2.me/theorems/6a41e351-8562-5876-9dc8-dc71d140ae54
-- title:
--   Local Counting Sum: sum cnt
-- statement:
--   The Local Counting Sum construction uses the sum cnt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensQ.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensQ.lean#L17-L29

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

theorem PI.VolStabW.LocalCountingSum.sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by sorry
