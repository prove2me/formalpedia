-- Prove2me | Theorems.Thm_PI_WFJM_pderiv_X_mul_monomial
-- name    : PI.WFJM.pderiv_X_mul_monomial
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:01.485063+00:00
-- url     : https://prove2.me/theorems/b3ea2095-282f-59bb-94ad-8782eb4f9edb
-- title:
--   WFJM: pderiv X mul monomial
-- statement:
--   The WFJM construction uses the pderiv X mul monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L66-L76

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

theorem PI.WFJM.pderiv_X_mul_monomial {σ : Type*} (i : σ) (α : σ →₀ ℕ) (c : ℂ) :
    pderiv i (X i * monomial α c) = (((α i : ℕ) : ℂ) + 1) • monomial α c := by sorry
