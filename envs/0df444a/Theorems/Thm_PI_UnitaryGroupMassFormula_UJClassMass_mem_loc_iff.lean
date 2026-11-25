-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mem_loc_iff
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.mem_loc_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:23.484893+00:00
-- url     : https://prove2.me/theorems/7b37e859-b27a-55fe-b1a9-88a6f4ac4298
-- title:
--   UJClass Mass: mem loc iff
-- statement:
--   The UJClass Mass construction uses the mem loc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjH.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjH.lean#L15-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.mem_loc_iff (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ loc (K := E) p L ↔ ∃ s ∈ hcompl (K := E) p, s • x ∈ L := by sorry
