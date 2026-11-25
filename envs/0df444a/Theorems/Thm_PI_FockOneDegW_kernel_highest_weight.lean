-- Prove2me | Theorems.Thm_PI_FockOneDegW_kernel_highest_weight
-- name    : PI.FockOneDegW.kernel_highest_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:27.60262+00:00
-- url     : https://prove2.me/theorems/7015ede4-c801-49b7-8111-14553ec5bd2f
-- title:
--   Fock One Deg W: kernel highest weight
-- statement:
--   The Fock One Deg W construction uses the kernel highest weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/RedOps.lean#L108-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/RedOps.lean#L108-L118

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
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
open PI.FockOneDegW.RedOps

theorem PI.FockOneDegW.kernel_highest_weight : KHc := by sorry
