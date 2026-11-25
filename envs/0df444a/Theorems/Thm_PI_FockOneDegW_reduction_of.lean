-- Prove2me | Theorems.Thm_PI_FockOneDegW_reduction_of
-- name    : PI.FockOneDegW.reduction_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:31.710477+00:00
-- url     : https://prove2.me/theorems/a801ff49-7053-530a-8ada-59b43ef26fa2
-- title:
--   Fock One Deg W: reduction of
-- statement:
--   The Fock One Deg W construction uses the reduction of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/SameBlockOfPosC.lean#L150-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/SameBlockOfPosC.lean#L150-L176

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW

theorem PI.FockOneDegW.reduction_of (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) : Reduction := by sorry
