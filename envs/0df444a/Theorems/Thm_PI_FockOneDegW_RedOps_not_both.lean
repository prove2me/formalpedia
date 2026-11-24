-- Prove2me | Theorems.Thm_PI_FockOneDegW_RedOps_not_both
-- name    : PI.FockOneDegW.RedOps.not_both
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:55.404803+00:00
-- url     : https://prove2.me/theorems/8df7da2d-d9a6-429f-8061-6a0377230a42
-- title:
--   Red Ops: not both
-- statement:
--   The Red Ops construction uses the not both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KernelHarmonic.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KernelHarmonic.lean#L46-L49

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KernelHarmonic
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
open PI PI.FockOneDegW PI.FockOneDegW.RedOps
open PI.FockOneDegW
variable {p q r s : ℕ}

theorem PI.FockOneDegW.RedOps.not_both (c d : Ix r s) (hcd : ¬ sameBlock c d) (a : Ix p q)
    (h1 : linePos ((a, c) : Ln p q r s) = true) (h2 : linePos ((a, d) : Ln p q r s) = true) :
    False := by sorry
