-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_upper
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.crd_upper
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:35.052967+00:00
-- url     : https://prove2.me/theorems/39c6c8a2-ab39-46d3-9328-473ee49914ec
-- title:
--   UJClass Mass: crd upper
-- statement:
--   The UJClass Mass construction uses the crd upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L17-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L17-L39

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.crd_upper {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (hfg : L0.FG) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ (y • x i) := by sorry
