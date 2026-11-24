-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_SS_self_re
-- name    : PI.FockOneDegW.Core.SS_self_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:30.969643+00:00
-- url     : https://prove2.me/theorems/dff38fb2-b215-4d2e-bc67-0a196fabf488
-- title:
--   Core: SS self re
-- statement:
--   The Core construction uses the SS self re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L128-L133

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
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
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}

theorem PI.FockOneDegW.Core.SS_self_re (v : Pol p q r s) (a : Ix p q) :
    (SS v a a).re = ∑ c : Ix r s, ∑ d : Ix r s, (fockInner (gg v a c d) (gg v a c d)).re := by sorry
