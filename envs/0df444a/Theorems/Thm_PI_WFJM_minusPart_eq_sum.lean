-- Prove2me | Theorems.Thm_PI_WFJM_minusPart_eq_sum
-- name    : PI.WFJM.minusPart_eq_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:27.666365+00:00
-- url     : https://prove2.me/theorems/a2392256-c04b-4be9-a427-7dd316c45bf3
-- title:
--   WFJM: minus Part eq sum
-- statement:
--   The WFJM construction uses the minus Part eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L359-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L359-L370

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
open MvPolynomial
variable {σ : Type*}

theorem PI.WFJM.minusPart_eq_sum (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart A P = ∑ d ∈ Finset.range (P.totalDegree + 1),
      homogeneousComponent d (A (homogeneousComponent (d + 2) P)) := by sorry
