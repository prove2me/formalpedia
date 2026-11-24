-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_den
-- name    : PI.UnitaryGroupMassFormula.UJClassFin.den
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:00.239977+00:00
-- url     : https://prove2.me/theorems/0e4a67fb-213a-43f3-acce-ad3c1cfb69c7
-- title:
--   UJClass Fin: den
-- statement:
--   The UJClass Fin construction uses the den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassFiniteness/IsIntegralOfIntOE.lean#L69-L83

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

theorem PI.UnitaryGroupMassFormula.UJClassFin.den (r : Af F ⊗[F] E) : ∃ m : ℕ, 0 < m ∧ m • r ∈ Oh F E := by sorry
