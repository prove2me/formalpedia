-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_isIntegral_of_intOE
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.isIntegral_of_intOE
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:50:19.460005+00:00
-- url     : https://prove2.me/theorems/2ad4532e-5757-4dff-b57e-ff204c4f67b6
-- title:
--   UJClass Fin: is Integral of int OE
-- statement:
--   The UJClass Fin construction uses the is Integral of int OE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L57-L59

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassFin.isIntegral_of_intOE {e : E} (he : e ∈ Formalism.UG.intOE E) : IsIntegral ℤ e := by sorry
