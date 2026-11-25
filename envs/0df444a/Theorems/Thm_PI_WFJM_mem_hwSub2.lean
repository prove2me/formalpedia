-- Prove2me | Theorems.Thm_PI_WFJM_mem_hwSub2
-- name    : PI.WFJM.mem_hwSub2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:44:01.031935+00:00
-- url     : https://prove2.me/theorems/9ed2265e-9268-4c96-b161-94dfd7da9bd3
-- title:
--   WFJM: mem hw Sub2
-- statement:
--   The WFJM construction uses the mem hw Sub2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L672-L680
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LoweringPartRightActionInlInr.lean#L672-L680

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
variable {p q r s : ℕ}
open MvPolynomial

theorem PI.WFJM.mem_hwSub2 (μ : Ix r s → ℚ) (P : Pol p q r s) :
    P ∈ hwSub (fockAct2 p q r s) μ ↔
      (∀ m ∈ P.support, ∀ c, (wt2 m c : ℚ) + sh2 p q r s c = μ c) ∧
        ∀ c d, posC c d → rai2 (p := p) (q := q) c d P = 0 := by sorry
