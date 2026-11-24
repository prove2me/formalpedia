-- Prove2me | Theorems.Thm_PI_FJMP_mem_rightHighestWeight_of_isMinimalJointVector
-- name    : PI.FJMP.mem_rightHighestWeight_of_isMinimalJointVector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:13.629899+00:00
-- url     : https://prove2.me/theorems/1159f5f5-61c6-4098-a5f3-bc816b2d1cf3
-- title:
--   FJMP: mem right Highest Weight of is Minimal Joint Vector
-- statement:
--   The FJMP construction uses the mem right Highest Weight of is Minimal Joint Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L290-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L290-L296

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

theorem PI.FJMP.mem_rightHighestWeight_of_isMinimalJointVector {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : P ∈ hwSub (fockAct2 p q r s) μ' := by sorry
