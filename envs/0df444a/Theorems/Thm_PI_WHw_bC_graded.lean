-- Prove2me | Theorems.Thm_PI_WHw_bC_graded
-- name    : PI.WHw.bC_graded
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:28.886321+00:00
-- url     : https://prove2.me/theorems/4281947a-7fc8-4522-8fbf-6e3aa84e8eb8
-- title:
--   WHw: b C graded
-- statement:
--   The WHw construction uses the b C graded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/BCRowGenMonomial.lean#L156-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/BCRowGenMonomial.lean#L156-L186

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open PI PI.WHw

theorem PI.WHw.bC_graded {r n : ℕ} (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (hf : f ∈ M) (μ : Fin r → ℕ) :
    weightedHomogeneousComponent (rowW r n) μ f ∈ M := by sorry
