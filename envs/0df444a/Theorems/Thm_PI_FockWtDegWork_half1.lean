-- Prove2me | Theorems.Thm_PI_FockWtDegWork_half1
-- name    : PI.FockWtDegWork.half1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:08.525522+00:00
-- url     : https://prove2.me/theorems/e9336a54-1c32-46b1-ae1c-1f832844be44
-- title:
--   Fock Wt Deg Work: half1
-- statement:
--   The Fock Wt Deg Work construction uses the half1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L284-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L284-L297

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

theorem PI.FockWtDegWork.half1 (p q r s : ℕ) : ∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d →
    IsHW (fockAct1 p q r s) μ P → degW (cPair r s) μ ≤ d := by sorry
