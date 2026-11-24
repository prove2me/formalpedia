-- Prove2me | Theorems.Thm_PI_FJMP_pderiv_eq_zero_of_noVar
-- name    : PI.FJMP.pderiv_eq_zero_of_noVar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:42.240071+00:00
-- url     : https://prove2.me/theorems/6b6b127e-3310-4e4d-9d8e-224f2b5a24b3
-- title:
--   FJMP: pderiv eq zero of no Var
-- statement:
--   The FJMP construction uses the pderiv eq zero of no Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L42-L46

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

theorem PI.FJMP.pderiv_eq_zero_of_noVar {P : MvPolynomial σ ℂ} {v : σ} (h : NoVar P v) : pderiv v P = 0 := by sorry
