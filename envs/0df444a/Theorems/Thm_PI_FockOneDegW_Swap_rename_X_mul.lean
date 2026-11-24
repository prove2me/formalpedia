-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_rename_X_mul
-- name    : PI.FockOneDegW.Swap.rename_X_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:44.271864+00:00
-- url     : https://prove2.me/theorems/baaf2c1e-4d68-43ca-8707-0c1020a5239c
-- title:
--   Swap: rename X mul
-- statement:
--   The Swap construction uses the rename X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L103-L105

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

theorem PI.FockOneDegW.Swap.rename_X_mul (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (X l * P) = X (sw p q r s l) * rename (sw p q r s) P := by sorry
