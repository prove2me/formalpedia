-- Prove2me | Theorems.Thm_PI_FJMX_rightRootDerivation_X
-- name    : PI.FJMX.rightRootDerivation_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:27.204297+00:00
-- url     : https://prove2.me/theorems/72e1503f-6eeb-4c5b-a902-01c99483c1a2
-- title:
--   FJMX: right Root Derivation X
-- statement:
--   The FJMX construction uses the right Root Derivation X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L47-L67

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

theorem PI.FJMX.rightRootDerivation_X (c d : Ix r s) (v : Ln p q r s) :
    der2 c d (X v : Pol p q r s) = if linePos (v.1, c) = true then (if v.2 = d then X (v.1, c) else 0)
      else (if v.2 = c then -X (v.1, d) else 0) := by sorry
