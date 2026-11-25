-- Prove2me | Theorems.Thm_PI_FockOneDegW_sum_half
-- name    : PI.FockOneDegW.sum_half
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:36.955091+00:00
-- url     : https://prove2.me/theorems/1815d85c-8195-482f-83b6-980d39eee5ed
-- title:
--   Fock One Deg W: sum half
-- statement:
--   The Fock One Deg W construction uses the sum half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/FockOperatorsKernel.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/FockOperatorsKernel.lean#L64-L67

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW

theorem PI.FockOneDegW.sum_half {p q r s : ℕ} (a : Ix p q) :
    ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then (1 / 2 : ℂ) else -(1 / 2)) =
      (((kShift r s a : ℚ)) : ℂ) := by sorry
