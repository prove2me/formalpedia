-- Prove2me | Theorems.Thm_PI_WFJM_omE_self_monomial
-- name    : PI.WFJM.omE_self_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:20.26617+00:00
-- url     : https://prove2.me/theorems/b6585c06-fdd5-4d3b-895f-81cfd58a1413
-- title:
--   WFJM: om E self monomial
-- statement:
--   The WFJM construction uses the om E self monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L111-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L111-L127

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

theorem PI.WFJM.omE_self_monomial {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) (c : ℂ) :
    omE l l (monomial α c) = (sgnL l * (((α l : ℕ) : ℂ) + 1 / 2)) • monomial α c := by sorry
