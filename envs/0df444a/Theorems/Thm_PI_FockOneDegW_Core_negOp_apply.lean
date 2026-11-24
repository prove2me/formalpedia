-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_negOp_apply
-- name    : PI.FockOneDegW.Core.negOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:44.001141+00:00
-- url     : https://prove2.me/theorems/f418d934-c70e-40a9-b376-7f2473930e58
-- title:
--   Core: neg Op apply
-- statement:
--   The Core construction uses the neg Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L151-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L151-L159

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

theorem PI.FockOneDegW.Core.negOp_apply (v : Pol p q r s) (b a : Ix p q) :
    negOp b a v = ∑ c : Ix r s, (if linePos ((b, c) : Ln p q r s) = true then 0
      else X ((b, c) : Ln p q r s) * pderiv ((a, c) : Ln p q r s) v) := by sorry
