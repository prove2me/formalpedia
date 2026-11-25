-- Prove2me | Theorems.Thm_PI_FJMA_freeOf_union
-- name    : PI.FJMA.freeOf_union
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:51.972453+00:00
-- url     : https://prove2.me/theorems/8540991b-1951-4431-ad50-fb3b59cc47f3
-- title:
--   FJMA: free Of union
-- statement:
--   The FJMA construction uses the free Of union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L125-L130

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
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
open PI PI.FJMA
open PI.FJM
variable {σ : Type}

theorem PI.FJMA.freeOf_union {S T : Set σ} {G : MvPolynomial σ ℂ} (h1 : FreeOf S G) (h2 : FreeOf T G) :
    FreeOf (S ∪ T) G := by sorry
