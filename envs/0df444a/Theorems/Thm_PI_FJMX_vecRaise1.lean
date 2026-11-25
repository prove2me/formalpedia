-- Prove2me | Theorems.Thm_PI_FJMX_vecRaise1
-- name    : PI.FJMX.vecRaise1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:57.459664+00:00
-- url     : https://prove2.me/theorems/b54f622b-9d46-53c9-be23-35027ed9a0c0
-- title:
--   FJMX: vec Raise1
-- statement:
--   The FJMX construction uses the vec Raise1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L249-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L249-L309

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
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

theorem PI.FJMX.vecRaise1 (a b c d : List ℤ) (x y : Ix p q) (hxy : posC x y) :
    der1 (r := r) (s := s) x y (hwVec p q r s a b c d) = 0 := by sorry
