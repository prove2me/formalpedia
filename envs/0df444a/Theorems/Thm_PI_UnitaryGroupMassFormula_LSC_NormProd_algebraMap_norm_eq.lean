-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_NormProd_algebraMap_norm_eq
-- name    : PI.UnitaryGroupMassFormula.LSC.NormProd.algebraMap_norm_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:02.828688+00:00
-- url     : https://prove2.me/theorems/bebbac03-a6a5-4a15-b94c-b291f252e377
-- title:
--   Norm Prod: algebra Map norm eq
-- statement:
--   The Norm Prod construction uses the algebra Map norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/NormProd.lean#L12-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/NormProd.lean#L12-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_NormProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC PI.UnitaryGroupMassFormula.LSC.NormProd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.LSC.NormProd.algebraMap_norm_eq (hc : Formalism.BasicNotions.CMData F E) (m : E) :
    algebraMap F E (Algebra.norm F m) = m * star m := by sorry
