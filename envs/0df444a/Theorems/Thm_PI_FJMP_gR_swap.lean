-- Prove2me | Theorems.Thm_PI_FJMP_gR_swap
-- name    : PI.FJMP.gR_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:48.201822+00:00
-- url     : https://prove2.me/theorems/de23ad60-b123-405f-9ce9-0f2700a7f231
-- title:
--   FJMP: g R swap
-- statement:
--   The FJMP construction uses the g R swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L93-L98

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
variable {κ : Type*} [Fintype κ]

theorem PI.FJMP.gR_swap (u v : κ → σ) (pos : κ → Bool) (P : MvPolynomial σ ℂ) :
    gR v u (fun c => !pos c) P = -gR u v pos P := by sorry
