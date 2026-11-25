-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_lsLoc
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.lsLoc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:37.806269+00:00
-- url     : https://prove2.me/theorems/455777ef-d02d-4f60-b0cb-9d18697954d5
-- title:
--   UJClass Mass: ls Loc
-- statement:
--   The UJClass Mass construction uses the ls Loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSLocA.lean#L27-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSLocA.lean#L27-L123

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_SigRTmulOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass

theorem PI.UnitaryGroupMassFormula.UJClassMass.lsLoc : LSLoc := by sorry
