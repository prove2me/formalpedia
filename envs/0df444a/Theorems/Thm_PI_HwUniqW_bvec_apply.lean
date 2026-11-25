-- Prove2me | Theorems.Thm_PI_HwUniqW_bvec_apply
-- name    : PI.HwUniqW.bvec_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:32:12.339798+00:00
-- url     : https://prove2.me/theorems/6874229f-2e57-5d11-a15f-0babb5665e30
-- title:
--   Hw Uniq W: bvec apply
-- statement:
--   The Hw Uniq W construction uses the bvec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L246-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L246-L247

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
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
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}

theorem PI.HwUniqW.bvec_apply (i j : Fin (2 * r + k + 1)) : bvec j i = if i = j then 1 else 0 := by sorry
