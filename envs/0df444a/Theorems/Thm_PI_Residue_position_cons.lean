-- Prove2me | Theorems.Thm_PI_Residue_position_cons
-- name    : PI.Residue.position_cons
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:14.392797+00:00
-- url     : https://prove2.me/theorems/d37d4d12-2f0d-5729-8d22-f6639e8aa536
-- title:
--   Residue: position cons
-- statement:
--   The Residue construction uses the position cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

theorem PI.Residue.position_cons (N : α → ℕ) (idx : α → ι) (a : α) (s : Multiset α) (i : ι) :
    intersection_update_fsHerm_neg_one N idx (a ::ₘ s) i = (if idx a = i then N a else 1) * intersection_update_fsHerm_neg_one N idx s i := by sorry
