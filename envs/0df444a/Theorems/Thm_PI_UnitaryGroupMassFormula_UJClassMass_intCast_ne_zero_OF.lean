-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_intCast_ne_zero_OF
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.intCast_ne_zero_OF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:17.713997+00:00
-- url     : https://prove2.me/theorems/a154cee6-a869-4821-9e8c-aae30ce7b59a
-- title:
--   UJClass Mass: int Cast ne zero OF
-- statement:
--   The UJClass Mass construction uses the int Cast ne zero OF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L64-L65

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.intCast_ne_zero_OF (y : ℤ) (hy : y ≠ 0) : (y : 𝓞 F) ≠ 0 := by sorry
