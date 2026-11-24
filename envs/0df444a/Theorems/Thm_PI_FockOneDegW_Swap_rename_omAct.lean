-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_rename_omAct
-- name    : PI.FockOneDegW.Swap.rename_omAct
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:25.319088+00:00
-- url     : https://prove2.me/theorems/dde8a9c1-2577-4e57-832e-1c73bb6328d8
-- title:
--   Swap: rename om Act
-- statement:
--   The Swap construction uses the rename om Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L139-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L139-L148

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

theorem PI.FockOneDegW.Swap.rename_omAct (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    rename (sw p q r s) (omAct p q r s M P) =
      omAct r s p q (M.submatrix (sw p q r s).symm (sw p q r s).symm) (rename (sw p q r s) P) := by sorry
