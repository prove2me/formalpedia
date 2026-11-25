-- Prove2me | Theorems.Thm_PI_HookSteps_fockQ_zsmul_right
-- name    : PI.HookSteps.fockQ_zsmul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:07:20.516133+00:00
-- url     : https://prove2.me/theorems/910949be-fbac-5b7c-b2bc-50b411cf0682
-- title:
--   Hook Steps: fock Q zsmul right
-- statement:
--   The Hook Steps construction uses the fock Q zsmul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DeterminantAdjugate.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DeterminantAdjugate.lean#L53-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DeterminantAdjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps

theorem PI.HookSteps.fockQ_zsmul_right {σ : Type*} (z : ℤ) (f g : MvPolynomial σ ℚ) :
    fockQ f (z • g) = (z : ℚ) * fockQ f g := by sorry
