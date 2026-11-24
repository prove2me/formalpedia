-- Prove2me | Theorems.Thm_PI_FJMX_weight_fin
-- name    : PI.FJMX.weight_fin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:51.242109+00:00
-- url     : https://prove2.me/theorems/658dc365-e8f7-4a3a-9356-b826ed5e457a
-- title:
--   FJMX: weight fin
-- statement:
--   The FJMX construction uses the weight fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean#L21-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}

theorem PI.FJMX.weight_fin (w : Ln p q r s → ℕ) (m : Ln p q r s →₀ ℕ) :
    Finsupp.weight w m = ∑ v, m v * w v := by sorry
