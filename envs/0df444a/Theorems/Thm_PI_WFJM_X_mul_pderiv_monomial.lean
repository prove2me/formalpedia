-- Prove2me | Theorems.Thm_PI_WFJM_X_mul_pderiv_monomial
-- name    : PI.WFJM.X_mul_pderiv_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:48.695138+00:00
-- url     : https://prove2.me/theorems/2694b13b-4bc9-4a35-91dd-488629ad700b
-- title:
--   WFJM: X mul pderiv monomial
-- statement:
--   The WFJM construction uses the X mul pderiv monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L57-L64

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

theorem PI.WFJM.X_mul_pderiv_monomial {σ : Type*} (i : σ) (α : σ →₀ ℕ) (c : ℂ) :
    X i * pderiv i (monomial α c) = ((α i : ℕ) : ℂ) • monomial α c := by sorry
