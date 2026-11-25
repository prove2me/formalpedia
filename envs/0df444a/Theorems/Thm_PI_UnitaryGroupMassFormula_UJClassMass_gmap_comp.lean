-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_gmap_comp
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.gmap_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:43:22.242602+00:00
-- url     : https://prove2.me/theorems/27e5b27e-f9cb-4a46-b88b-0822fba89758
-- title:
--   UJClass Mass: gmap comp
-- statement:
--   The UJClass Mass construction uses the gmap comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/GmapLeLocS.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/GmapLeLocS.lean#L53-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassMass.gmap_comp (u w : V ≃ₗ[E] V) (X : Submodule (𝓞 E) V) : gmap (u * w) X = gmap u (gmap w X) := by sorry
