-- Prove2me | Theorems.Thm_PI_HwUniqW_block_mk
-- name    : PI.HwUniqW.block_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:38.285706+00:00
-- url     : https://prove2.me/theorems/996e6a3b-c6e8-4638-a4d3-5c71eb85ef70
-- title:
--   Hw Uniq W: block mk
-- statement:
--   The Hw Uniq W construction uses the block mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L40-L44

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

theorem PI.HwUniqW.block_mk {i : Fin (2 * r + k + 1)} (hi : InB k r i) (p : i.val - r < k) : bl k r ⟨i.val - r, p⟩ = i := by sorry
