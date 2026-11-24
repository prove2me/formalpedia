-- Prove2me | Theorems.Thm_PI_FockOneDegW_Core_posOp_apply
-- name    : PI.FockOneDegW.Core.posOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:54.025086+00:00
-- url     : https://prove2.me/theorems/bb6e9174-ef68-4e42-9e0a-6e6728f89159
-- title:
--   Core: pos Op apply
-- statement:
--   The Core construction uses the pos Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L161-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/ExistsMonomialWeight.lean#L161-L169

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

theorem PI.FockOneDegW.Core.posOp_apply (v : Pol p q r s) (a b : Ix p q) :
    posOp a b v = ∑ d : Ix r s, (if linePos ((a, d) : Ln p q r s) = true then
      X ((a, d) : Ln p q r s) * pderiv ((b, d) : Ln p q r s) v else 0) := by sorry
