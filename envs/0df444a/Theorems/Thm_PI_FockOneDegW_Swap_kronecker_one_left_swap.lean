-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_kronecker_one_left_swap
-- name    : PI.FockOneDegW.Swap.kronecker_one_left_swap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:33:10.917988+00:00
-- url     : https://prove2.me/theorems/843a875a-9e1b-52f2-9d10-faab9550239e
-- title:
--   Swap: kronecker one left swap
-- statement:
--   The Swap construction uses the kronecker one left swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L150-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L150-L155

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
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
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {p q r s : ℕ}

theorem PI.FockOneDegW.Swap.kronecker_one_left_swap (X : Mat p q) :
    ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X).submatrix
        (sw p q r s).symm (sw p q r s).symm =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat r s) X := by sorry
