-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_set_of_coords_inj
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.set_of_coords_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:38.598799+00:00
-- url     : https://prove2.me/theorems/0f4dbf90-06cc-454e-a646-9fab21ded5bd
-- title:
--   UJClass Mass: set of coords inj
-- statement:
--   The UJClass Mass construction uses the set of coords inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L131-L136

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.set_of_coords_inj {M : ℕ} (b : Module.Basis (Fin M) E V) {A A' : Set (Fin M → E)}
    (e : {v : V | b.equivFun v ∈ A} = {v | b.equivFun v ∈ A'}) : A = A' := by sorry
