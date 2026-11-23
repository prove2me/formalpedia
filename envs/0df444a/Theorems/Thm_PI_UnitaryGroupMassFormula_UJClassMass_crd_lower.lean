-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_lower
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.crd_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:07.292713+00:00
-- url     : https://prove2.me/theorems/c3d4ec70-8c00-4104-a76e-1b33adde40e7
-- title:
--   UJClass Mass: crd lower
-- statement:
--   The UJClass Mass construction uses the crd lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L48-L62

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.crd_lower {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    (hspan : Submodule.span E (L0 : Set V) = ⊤) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ i, y • b i ∈ L0 := by sorry
