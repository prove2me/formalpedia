-- Prove2me | Theorems.Thm_PI_FJM_minHyp_of_mem
-- name    : PI.FJM.minHyp_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:05.010349+00:00
-- url     : https://prove2.me/theorems/0ac99a03-fa38-4d33-b3f0-ecfb31e9fce5
-- title:
--   FJM: min Hyp of mem
-- statement:
--   The FJM construction uses the min Hyp of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/FockJointMultOfCauchy.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/FockJointMultOfCauchy.lean#L15-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsBlockHighestWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_FockJointMultOfCauchy
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
open PI PI.FJM

theorem PI.FJM.minHyp_of_mem {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hP : P ∈ JH p q r s μ μ') (h0 : P ≠ 0) : MinHyp p q r s μ μ' P := by sorry
