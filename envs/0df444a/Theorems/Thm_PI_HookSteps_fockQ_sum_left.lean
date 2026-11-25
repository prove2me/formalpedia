-- Prove2me | Theorems.Thm_PI_HookSteps_fockQ_sum_left
-- name    : PI.HookSteps.fockQ_sum_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:17:13.267209+00:00
-- url     : https://prove2.me/theorems/9784ea7d-0b08-46be-958d-928deec76ded
-- title:
--   Hook Steps: fock Q sum left
-- statement:
--   The Hook Steps construction uses the fock Q sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DeterminantAdjugate.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DeterminantAdjugate.lean#L32-L36

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

theorem PI.HookSteps.fockQ_sum_left {σ ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) (g : MvPolynomial σ ℚ) :
    fockQ (∑ i ∈ s, F i) g = ∑ i ∈ s, fockQ (F i) g := by sorry
