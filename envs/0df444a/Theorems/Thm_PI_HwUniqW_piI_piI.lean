-- Prove2me | Theorems.Thm_PI_HwUniqW_piI_piI
-- name    : PI.HwUniqW.piI_piI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:27.572939+00:00
-- url     : https://prove2.me/theorems/25475890-bb65-4d0c-a307-10efcc99b4cf
-- title:
--   Hw Uniq W: pi I pi I
-- statement:
--   The Hw Uniq W construction uses the pi I pi I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L23-L27

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

theorem PI.HwUniqW.piI_piI (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by sorry
