-- Prove2me | Theorems.Thm_PI_FockOneDegW_negOp_apply
-- name    : PI.FockOneDegW.negOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:31.382807+00:00
-- url     : https://prove2.me/theorems/574677fa-14dc-4bdc-a673-0df00a7e83a4
-- title:
--   Fock One Deg W: neg Op apply
-- statement:
--   The Fock One Deg W construction uses the neg Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/FockOperatorsKernel.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/FockOperatorsKernel.lean#L56-L62

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

theorem PI.FockOneDegW.negOp_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    negOp a b P = ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then 0 else
      X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P) := by sorry
