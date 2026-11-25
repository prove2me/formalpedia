-- Prove2me | Theorems.Thm_PI_FockWtDegWork_fockAct2_diag
-- name    : PI.FockWtDegWork.fockAct2_diag
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:39.674272+00:00
-- url     : https://prove2.me/theorems/5a314178-16c8-456d-925e-2c891f2bc93b
-- title:
--   Fock Wt Deg Work: fock Act2 diag
-- statement:
--   The Fock Wt Deg Work construction uses the fock Act2 diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L113-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L113-L134

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

theorem PI.FockWtDegWork.fockAct2_diag (p q r s : ℕ) (c : Ix r s) :
    fockAct2 p q r s (Eab c c) = ∑ a : Ix p q, omE ((a, c) : Ln p q r s) (a, c) := by sorry
