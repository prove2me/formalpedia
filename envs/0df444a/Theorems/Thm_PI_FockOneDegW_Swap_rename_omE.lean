-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_rename_omE
-- name    : PI.FockOneDegW.Swap.rename_omE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:42.132146+00:00
-- url     : https://prove2.me/theorems/75cdfcb7-ddf8-4716-a9d0-590a7ccdc1ca
-- title:
--   Swap: rename om E
-- statement:
--   The Swap construction uses the rename om E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L127-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L127-L137

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

theorem PI.FockOneDegW.Swap.rename_omE (l l' : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (omE l l' P) =
      omE (sw p q r s l) (sw p q r s l') (rename (sw p q r s) P) := by sorry
