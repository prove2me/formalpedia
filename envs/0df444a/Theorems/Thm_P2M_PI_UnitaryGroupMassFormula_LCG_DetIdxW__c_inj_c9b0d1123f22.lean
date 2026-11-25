-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_inj_c9b0d1123f22
-- name    : P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_inj_c9b0d1123f22
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:01:10.158801+00:00
-- url     : https://prove2.me/theorems/a7727e79-6ce9-5427-9733-c7d64404ae11
-- title:
--   P2 M PI Unitary Group Mass Formula LCG Det Idx W  c inj c9b0d1123f22: P2 M PI Unitary Group Mass Formula LCG Det Idx W  c inj c9b0d1123f22
-- statement:
--   The P2 M PI Unitary Group Mass Formula LCG Det Idx W  c inj c9b0d1123f22 construction uses the P2 M PI Unitary Group Mass Formula LCG Det Idx W  c inj c9b0d1123f22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDet.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDet.lean#L19-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DetIdxW
variable {K : Type} [Field K] [NumberField K] {k : ℕ}

theorem P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_inj_c9b0d1123f22 : Function.Injective (ιc K k) := by sorry

alias «PI».«UnitaryGroupMassFormula».«LCG».«DetIdxW».«ιc_inj» := P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_inj_c9b0d1123f22
