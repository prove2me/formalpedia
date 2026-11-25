-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_inj
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.linOf_inj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:42.00592+00:00
-- url     : https://prove2.me/theorems/a5bfe856-ba4a-5167-940f-655e83093b56
-- title:
--   UJClass Mass: lin Of inj
-- statement:
--   The UJClass Mass construction uses the lin Of inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/CardStepOf.lean#L72-L76

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
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.linOf_inj {M : ℕ} (b : Module.Basis (Fin M) E V) {U U' : GL (Fin M) E}
    (e : linOf b U = linOf b U') : U = U' := by sorry
