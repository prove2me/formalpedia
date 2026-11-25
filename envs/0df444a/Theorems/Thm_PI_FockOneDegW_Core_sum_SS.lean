-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_sum_SS
-- name    : PI.FockOneDegW.Core.sum_SS
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:53.926855+00:00
-- url     : https://prove2.me/theorems/f66373b6-34ae-4dbc-af5d-44e48c97392f
-- title:
--   Core: sum SS
-- statement:
--   The Core construction uses the sum SS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L96-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L96-L118

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

theorem PI.FockOneDegW.Core.sum_SS (v : Pol p q r s)
    (hH : ∀ c d : Ix r s, ¬ sameBlock c d → lowOp (p := p) (q := q) c d v = 0) :
    ∑ a : Ix p q, ∑ b : Ix p q, SS v a b = 0 := by sorry
