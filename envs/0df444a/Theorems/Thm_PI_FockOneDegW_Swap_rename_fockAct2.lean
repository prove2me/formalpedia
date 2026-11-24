-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_rename_fockAct2
-- name    : PI.FockOneDegW.Swap.rename_fockAct2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:22.267592+00:00
-- url     : https://prove2.me/theorems/258f1358-87a9-4a14-b111-9ed8e6a28b9f
-- title:
--   Swap: rename fock Act2
-- statement:
--   The Swap construction uses the rename fock Act2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L169-L172

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

theorem PI.FockOneDegW.Swap.rename_fockAct2 (Y : Mat r s) (P : Pol p q r s) :
    rename (sw p q r s) (fockAct2 p q r s Y P) = fockAct1 r s p q Y (rename (sw p q r s) P) := by sorry
