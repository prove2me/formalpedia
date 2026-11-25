-- Prove2me | Theorems.Thm_PI_WFJM_sum_hc_of_le
-- name    : PI.WFJM.sum_hc_of_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:46.705702+00:00
-- url     : https://prove2.me/theorems/63e1dc67-6fe2-59c2-9e3b-89cb5148c29f
-- title:
--   WFJM: sum hc of le
-- statement:
--   The WFJM construction uses the sum hc of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L341-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L341-L357

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

theorem PI.WFJM.sum_hc_of_le (P : MvPolynomial σ ℂ) (n : ℕ) (hn : P.totalDegree < n) :
    ∑ i ∈ Finset.range n, homogeneousComponent i P = P := by sorry
