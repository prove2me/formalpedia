-- Prove2me | Theorems.Thm_PI_FJMX_leftRootDerivation_X
-- name    : PI.FJMX.leftRootDerivation_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:54.291809+00:00
-- url     : https://prove2.me/theorems/63ec0ef5-3e87-4b74-aa75-0e2643d56b39
-- title:
--   FJMX: left Root Derivation X
-- statement:
--   The FJMX construction uses the left Root Derivation X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L25-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistHW.lean#L25-L45

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

theorem PI.FJMX.leftRootDerivation_X (a b : Ix p q) (v : Ln p q r s) :
    der1 a b (X v : Pol p q r s) = if linePos (a, v.2) = true then (if v.1 = b then X (a, v.2) else 0)
      else (if v.1 = a then -X (b, v.2) else 0) := by sorry
