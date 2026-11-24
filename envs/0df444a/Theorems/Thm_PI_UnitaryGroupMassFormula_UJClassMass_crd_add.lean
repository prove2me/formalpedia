-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_add
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.crd_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:18.544651+00:00
-- url     : https://prove2.me/theorems/5e070c90-d074-4c53-b55f-2e2cd240cec4
-- title:
--   UJClass Mass: crd add
-- statement:
--   The UJClass Mass construction uses the crd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSBase.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSBase.lean#L19-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassMass.crd_add (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {x y : Fin M → E}
    (hx : x ∈ crdOf b L0) (hy : y ∈ crdOf b L0) : x + y ∈ crdOf b L0 := by sorry
