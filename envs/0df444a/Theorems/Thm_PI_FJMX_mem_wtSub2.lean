-- Prove2me | Theorems.Thm_PI_FJMX_mem_wtSub2
-- name    : PI.FJMX.mem_wtSub2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:08.808962+00:00
-- url     : https://prove2.me/theorems/be1ec88c-f976-4fce-a0e4-68ba001c4ecc
-- title:
--   FJMX: mem wt Sub2
-- statement:
--   The FJMX construction uses the mem wt Sub2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean#L88-L95

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

theorem PI.FJMX.mem_wtSub2 (hW : FormWt2) (P : Pol p q r s) (μ : Ix r s → ℚ)
    (h : ∀ y, ∃ W : ℤ, (W : ℚ) + sh2 p q r s y = μ y ∧ ∀ m, coeff m P ≠ 0 → wt2 m y = W) :
    P ∈ wtSub (fockAct2 p q r s) μ := by sorry
