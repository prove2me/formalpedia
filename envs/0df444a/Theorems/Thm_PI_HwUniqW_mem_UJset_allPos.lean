-- Prove2me | Theorems.Thm_PI_HwUniqW_mem_UJset_allPos
-- name    : PI.HwUniqW.mem_UJset_allPos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:13.999579+00:00
-- url     : https://prove2.me/theorems/9fd78754-ee4d-46e1-a859-874944fd27be
-- title:
--   Hw Uniq W: mem UJset all Pos
-- statement:
--   The Hw Uniq W construction uses the mem UJset all Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L223-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L223-L226

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

theorem PI.HwUniqW.mem_UJset_allPos {h : Matrix (Fin k) (Fin k) ℂ} : h ∈ UJset (allPos k) ↔ hᴴ * h = 1 := by sorry
