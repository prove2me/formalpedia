-- Prove2me | Theorems.Thm_PI_FJMA_freeOf_of_mul
-- name    : PI.FJMA.freeOf_of_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:31:23.576274+00:00
-- url     : https://prove2.me/theorems/1a963503-21c5-5056-88d5-ac311ef90629
-- title:
--   FJMA: free Of of mul
-- statement:
--   The FJMA construction uses the free Of of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L58-L64

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

theorem PI.FJMA.freeOf_of_mul {S T : Set σ} {F G : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) (hF0 : F ≠ 0)
    (hG : FreeOf S G) (hH : FreeOf T (F * G)) (hST : Disjoint S T) : FreeOf T G := by sorry
