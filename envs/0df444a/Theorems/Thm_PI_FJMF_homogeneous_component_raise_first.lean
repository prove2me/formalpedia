-- Prove2me | Theorems.Thm_PI_FJMF_homogeneous_component_raise_first
-- name    : PI.FJMF.homogeneous_component_raise_first
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:39.591653+00:00
-- url     : https://prove2.me/theorems/178a27d1-8776-4987-aabc-c273a9d47d6f
-- title:
--   FJMF: homogeneous component raise first
-- statement:
--   The FJMF construction uses the homogeneous component raise first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MinDeg.lean#L149-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MinDeg.lean#L149-L153

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
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
open PI PI.FJMF
variable {p q r s : ℕ}

theorem PI.FJMF.homogeneous_component_raise_first {a b : Ix p q} (hab : sameBlock a b) (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e (PI.FJM.rai1 (r := r) (s := s) a b Q) =
      PI.FJM.rai1 (r := r) (s := s) a b (homogeneousComponent e Q) := by sorry
