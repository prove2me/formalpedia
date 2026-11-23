-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_int_smul_mem
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.int_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:20.56507+00:00
-- url     : https://prove2.me/theorems/84c8c1c8-3991-464d-953a-858bc8026e81
-- title:
--   UJClass Mass: int smul mem
-- statement:
--   The UJClass Mass construction uses the int smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L41-L46

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.int_smul_mem (L0 : Submodule (𝓞 E) V) {e : E} (he : IsIntegral ℤ e) {v : V} (hv : v ∈ L0) :
    e • v ∈ L0 := by sorry
