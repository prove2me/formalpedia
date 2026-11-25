-- Prove2me | Theorems.Thm_PI_FJMF_hc_mem_hwSub2
-- name    : PI.FJMF.hc_mem_hwSub2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:31.979114+00:00
-- url     : https://prove2.me/theorems/34b6d1a9-565a-42f5-bea9-e83229b06ac9
-- title:
--   FJMF: hc mem hw Sub2
-- statement:
--   The FJMF construction uses the hc mem hw Sub2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MinDeg.lean#L167-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MinDeg.lean#L167-L171

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

theorem PI.FJMF.hc_mem_hwSub2 (μ : Ix r s → ℚ) (P : Pol p q r s) (hP : P ∈ hwSub (fockAct2 p q r s) μ) (e : ℕ) :
    homogeneousComponent e P ∈ hwSub (fockAct2 p q r s) μ := by sorry
