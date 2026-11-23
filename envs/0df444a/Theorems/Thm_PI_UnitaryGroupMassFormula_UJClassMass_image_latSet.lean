-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_image_latSet
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.image_latSet
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:55.696173+00:00
-- url     : https://prove2.me/theorems/345f3a96-1e4e-4bea-918a-2fb3a0702543
-- title:
--   UJClass Mass: image lat Set
-- statement:
--   The UJClass Mass construction uses the image lat Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L112-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L112-L129

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.image_latSet (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) (U : GL (Fin M) E) (g : HA (AF F) σ J) :
    (linOf b U : V → V) '' latSet σ J b L0 g =
      {v | b.equivFun v ∈ (fun x => (U : Matrix (Fin M) (Fin M) E).mulVec x) ''
        PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g} := by sorry
