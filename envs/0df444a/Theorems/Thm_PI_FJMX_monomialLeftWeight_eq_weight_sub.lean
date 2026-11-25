-- Prove2me | Theorems.Thm_PI_FJMX_monomialLeftWeight_eq_weight_sub
-- name    : PI.FJMX.monomialLeftWeight_eq_weight_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:08.016435+00:00
-- url     : https://prove2.me/theorems/906d5e26-8d81-4bec-930e-eec7de3938dd
-- title:
--   FJMX: monomial Left Weight eq weight sub
-- statement:
--   The FJMX construction uses the monomial Left Weight eq weight sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean#L26-L39

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

theorem PI.FJMX.monomialLeftWeight_eq_weight_sub (m : Ln p q r s →₀ ℕ) (x : Ix p q) :
    wt1 m x = (Finsupp.weight (leftPositiveIndicator x) m : ℤ) - (Finsupp.weight (leftNegativeIndicator x) m : ℤ) := by sorry
