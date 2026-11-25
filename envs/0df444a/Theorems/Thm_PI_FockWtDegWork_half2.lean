-- Prove2me | Theorems.Thm_PI_FockWtDegWork_half2
-- name    : PI.FockWtDegWork.half2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:31:07.636431+00:00
-- url     : https://prove2.me/theorems/7c98ac81-38bd-48dd-b6a3-53519f51fbc4
-- title:
--   Fock Wt Deg Work: half2
-- statement:
--   The Fock Wt Deg Work construction uses the half2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L299-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L299-L312

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

theorem PI.FockWtDegWork.half2 (p q r s : ℕ) : ∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d →
    IsHW (fockAct2 p q r s) μ P → degW (cPair p q) μ ≤ d := by sorry
