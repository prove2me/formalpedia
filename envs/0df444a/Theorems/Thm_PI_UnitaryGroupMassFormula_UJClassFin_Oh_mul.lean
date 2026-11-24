-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Oh_mul
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.Oh_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:03.913013+00:00
-- url     : https://prove2.me/theorems/500c22c7-a5c2-41fe-9157-abdf6cc09366
-- title:
--   UJClass Fin: Oh mul
-- statement:
--   The UJClass Fin construction uses the Oh mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L28-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L28-L55

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.Oh_mul {x y : Af F ⊗[F] E} (hx : x ∈ Oh F E) (hy : y ∈ Oh F E) : x * y ∈ Oh F E := by sorry
