-- Prove2me | Theorems.Thm_PI_HookSteps_fockQ_sum_right
-- name    : PI.HookSteps.fockQ_sum_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:05.512001+00:00
-- url     : https://prove2.me/theorems/1779d61e-7797-5c9b-a0e1-0f0913d51a19
-- title:
--   Hook Steps: fock Q sum right
-- statement:
--   The Hook Steps construction uses the fock Q sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DeterminantAdjugate.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DeterminantAdjugate.lean#L38-L42

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

theorem PI.HookSteps.fockQ_sum_right {σ ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) (f : MvPolynomial σ ℚ) :
    fockQ f (∑ i ∈ s, F i) = ∑ i ∈ s, fockQ f (F i) := by sorry
