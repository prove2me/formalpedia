-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_rename_fockAct1
-- name    : PI.FockOneDegW.Swap.rename_fockAct1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:59.84996+00:00
-- url     : https://prove2.me/theorems/86bbdd05-d124-46fd-9e41-c97670454c6e
-- title:
--   Swap: rename fock Act1
-- statement:
--   The Swap construction uses the rename fock Act1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L164-L167

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

theorem PI.FockOneDegW.Swap.rename_fockAct1 (X : Mat p q) (P : Pol p q r s) :
    rename (sw p q r s) (fockAct1 p q r s X P) = fockAct2 r s p q X (rename (sw p q r s) P) := by sorry
