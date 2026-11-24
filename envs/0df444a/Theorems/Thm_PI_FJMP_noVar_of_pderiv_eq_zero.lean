-- Prove2me | Theorems.Thm_PI_FJMP_noVar_of_pderiv_eq_zero
-- name    : PI.FJMP.noVar_of_pderiv_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:56.768552+00:00
-- url     : https://prove2.me/theorems/348914d0-cc37-4091-a3ae-cb8430c27ff7
-- title:
--   FJMP: no Var of pderiv eq zero
-- statement:
--   The FJMP construction uses the no Var of pderiv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L57-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L57-L79

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

theorem PI.FJMP.noVar_of_pderiv_eq_zero {P : MvPolynomial σ ℂ} {v : σ} (h : pderiv v P = 0) : NoVar P v := by sorry
