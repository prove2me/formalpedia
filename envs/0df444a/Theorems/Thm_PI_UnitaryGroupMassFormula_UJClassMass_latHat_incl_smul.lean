-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_latHat_incl_smul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.latHat_incl_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:45.51529+00:00
-- url     : https://prove2.me/theorems/b8ede1d6-22cc-5cbe-ad58-c7c3fe497026
-- title:
--   UJClass Mass: lat Hat incl smul
-- statement:
--   The UJClass Mass construction uses the lat Hat incl smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSBase.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSBase.lean#L93-L96

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.latHat_incl_smul (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {e : E}
    (he : IsIntegral ℤ e) {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E (crdOf b L0)) :
    inclR (F := F) (Af F) e • y ∈ latHat F E (crdOf b L0) := by sorry
