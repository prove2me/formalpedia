-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_inclR_injective
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.inclR_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:42:18.149044+00:00
-- url     : https://prove2.me/theorems/d7d2dd8f-adda-4ceb-8935-177a203c7d9c
-- title:
--   UJClass Mass: incl R injective
-- statement:
--   The UJClass Mass construction uses the incl R injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L33-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassMass.inclR_injective : Function.Injective (inclR (AF F) : E →+* AF F ⊗[F] E) := by sorry
