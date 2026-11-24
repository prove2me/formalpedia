-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_tmul_mem_Oh
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.tmul_mem_Oh
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:25.29486+00:00
-- url     : https://prove2.me/theorems/8d04aa49-b3b5-4a48-bc7d-251506b46870
-- title:
--   UJClass Fin: tmul mem Oh
-- statement:
--   The UJClass Fin construction uses the tmul mem Oh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L26-L26

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.tmul_mem_Oh {a : Af F} (ha : a ∈ intAf F) {e : E} (he : IsIntegral ℤ e) : a ⊗ₜ[F] e ∈ Oh F E := by sorry
