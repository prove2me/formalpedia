-- Prove2me | Theorems.Thm_PI_FJMA_shapeProd_supported
-- name    : PI.FJMA.shapeProd_supported
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:32:12.348801+00:00
-- url     : https://prove2.me/theorems/d1f7c767-0fed-50ae-858c-f585ae88765c
-- title:
--   FJMA: shape Prod supported
-- statement:
--   The FJMA construction uses the shape Prod supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/VarsZeroOfSupported.lean#L80-L84

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

theorem PI.FJMA.shapeProd_supported {m n : ℕ} (ι : Fin m × Fin n → σ) (α : List ℕ) :
    shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) α ∈ supported ℂ (Set.range ι) := by sorry
