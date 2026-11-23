-- Prove2me | Theorems.Thm_PI_HwUniqW_epsI_piI
-- name    : PI.HwUniqW.epsI_piI
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:00.724461+00:00
-- url     : https://prove2.me/theorems/d218bc86-878d-426d-8820-3aede15312f2
-- title:
--   Hw Uniq W: eps I pi I
-- statement:
--   The Hw Uniq W construction uses the eps I pi I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L29-L32

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
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

theorem PI.HwUniqW.epsI_piI (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by sorry
