-- Prove2me | Theorems.Thm_PI_HwUniqW_mk_bl
-- name    : PI.HwUniqW.mk_bl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:50.105114+00:00
-- url     : https://prove2.me/theorems/c68a766f-a30d-4f87-abaf-b932375ff50a
-- title:
--   Hw Uniq W: mk bl
-- statement:
--   The Hw Uniq W construction uses the mk bl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L35-L38

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

theorem PI.HwUniqW.mk_bl (c : Fin k) (p : (bl k r c).val - r < k) : (⟨(bl k r c).val - r, p⟩ : Fin k) = c := by sorry
