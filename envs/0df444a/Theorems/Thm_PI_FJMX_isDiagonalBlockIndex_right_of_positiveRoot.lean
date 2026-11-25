-- Prove2me | Theorems.Thm_PI_FJMX_isDiagonalBlockIndex_right_of_positiveRoot
-- name    : PI.FJMX.isDiagonalBlockIndex_right_of_positiveRoot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:35.048886+00:00
-- url     : https://prove2.me/theorems/cd208719-b5b8-47d6-94e0-b971934800e9
-- title:
--   FJMX: is Diagonal Block Index right of positive Root
-- statement:
--   The FJMX construction uses the is Diagonal Block Index right of positive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/IsDiagonalBlockIndexRightOfPositiveRoot.lean#L103-L104

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

theorem PI.FJMX.isDiagonalBlockIndex_right_of_positiveRoot (x y : Ix r s) (h : posC x y) (a : Ix p q) : linePos (a, x) = linePos (a, y) := by sorry
