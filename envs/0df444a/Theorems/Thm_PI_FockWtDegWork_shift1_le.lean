-- Prove2me | Theorems.Thm_PI_FockWtDegWork_shift1_le
-- name    : PI.FockWtDegWork.shift1_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:33:28.407105+00:00
-- url     : https://prove2.me/theorems/bcf9fdd9-cb8e-5e72-be30-e37e629b95b5
-- title:
--   Fock Wt Deg Work: shift1 le
-- statement:
--   The Fock Wt Deg Work construction uses the shift1 le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L230-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L230-L255

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork

theorem PI.FockWtDegWork.shift1_le {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) (a : Ix p q) :
    |shiftNu (cPair r s) (fun b => W1 b α) a| ≤ ∑ c : Ix r s, (α (a, c) : ℚ) := by sorry
