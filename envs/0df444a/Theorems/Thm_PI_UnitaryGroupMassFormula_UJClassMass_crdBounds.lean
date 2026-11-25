-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crdBounds
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.crdBounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:27.097801+00:00
-- url     : https://prove2.me/theorems/156e6add-11e1-4057-a7a4-fef309281513
-- title:
--   UJClass Mass: crd Bounds
-- statement:
--   The UJClass Mass construction uses the crd Bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L69-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/UJClassMassOfDeep.lean#L69-L80

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.crdBounds : CrdBounds := by sorry
