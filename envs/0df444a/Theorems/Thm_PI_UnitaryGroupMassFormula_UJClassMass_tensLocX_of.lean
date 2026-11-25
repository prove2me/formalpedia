-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_tensLocX_of
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.tensLocX_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:20:22.000875+00:00
-- url     : https://prove2.me/theorems/2076799d-4941-5925-8521-671e7091e7f0
-- title:
--   UJClass Mass: tens Loc X of
-- statement:
--   The UJClass Mass construction uses the tens Loc X of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L160-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L160-L214

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_TcoordBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
open HX

theorem PI.UnitaryGroupMassFormula.UJClassMass.tensLocX_of (hI : LocInt) : TensLoc := by sorry
