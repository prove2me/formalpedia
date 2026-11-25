-- Prove2me | Theorems.Thm_PI_HookSteps_fockQ_listX
-- name    : PI.HookSteps.fockQ_listX
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:48.481705+00:00
-- url     : https://prove2.me/theorems/4b2efbfe-f3c8-4685-9f1e-d26341b95b00
-- title:
--   Hook Steps: fock Q list X
-- statement:
--   The Hook Steps construction uses the fock Q list X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DeterminantAdjugate.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DeterminantAdjugate.lean#L62-L71

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DeterminantAdjugate
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem PI.HookSteps.fockQ_listX (hX : MulXAdj) {σ : Type} (l : List σ) (f g : MvPolynomial σ ℚ) :
    fockQ ((l.map fun v => (X v : MvPolynomial σ ℚ)).prod * f) g =
      fockQ f ((l.map fun v => ((pderiv v : Derivation ℚ _ _).toLinearMap :
        Module.End ℚ (MvPolynomial σ ℚ))).prod g) := by sorry
