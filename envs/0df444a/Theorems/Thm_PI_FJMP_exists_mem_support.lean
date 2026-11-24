-- Prove2me | Theorems.Thm_PI_FJMP_exists_mem_support
-- name    : PI.FJMP.exists_mem_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:08.141499+00:00
-- url     : https://prove2.me/theorems/b2f3933b-9b53-4126-93d3-8e6726e26b76
-- title:
--   FJMP: exists mem support
-- statement:
--   The FJMP construction uses the exists mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L81-L83

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

theorem PI.FJMP.exists_mem_support {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : ∃ e, e ∈ P.support := by sorry
