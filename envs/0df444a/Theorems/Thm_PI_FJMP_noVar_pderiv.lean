-- Prove2me | Theorems.Thm_PI_FJMP_noVar_pderiv
-- name    : PI.FJMP.noVar_pderiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:16.213439+00:00
-- url     : https://prove2.me/theorems/4b571433-3e89-4595-9675-877baf356863
-- title:
--   FJMP: no Var pderiv
-- statement:
--   The FJMP construction uses the no Var pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L48-L55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}

theorem PI.FJMP.noVar_pderiv {P : MvPolynomial σ ℂ} {v : σ} (h : NoVar P v) (u : σ) : NoVar (pderiv u P) v := by sorry
