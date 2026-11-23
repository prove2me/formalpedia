-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mem_iff_crdOf
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.mem_iff_crdOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:06.433276+00:00
-- url     : https://prove2.me/theorems/98a1c921-1fbe-4fe5-86f5-84244fb9cdbd
-- title:
--   UJClass Mass: mem iff crd Of
-- statement:
--   The UJClass Mass construction uses the mem iff crd Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSSkeleton.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSSkeleton.lean#L57-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.mem_iff_crdOf {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (v : V) :
    v ∈ L0 ↔ b.equivFun v ∈ crdOf b L0 := by sorry
