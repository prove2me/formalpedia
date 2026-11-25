-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_mul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.linOf_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:19.407736+00:00
-- url     : https://prove2.me/theorems/75a7d395-665a-4cd3-bdeb-e347a58248e5
-- title:
--   UJClass Mass: lin Of mul
-- statement:
--   The UJClass Mass construction uses the lin Of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LatticesCloseLocally.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LatticesCloseLocally.lean#L15-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermCL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LatticesCloseLocally
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {M : ℕ}

theorem PI.UnitaryGroupMassFormula.UJClassMass.linOf_mul (b : Module.Basis (Fin M) E V) (u w : GL (Fin M) E) :
    linOf b (u * w) = linOf b u * linOf b w := by sorry
