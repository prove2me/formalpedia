-- Prove2me | Theorems.Thm_PI_Residue_prod_position
-- name    : PI.Residue.prod_position
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:23.423447+00:00
-- url     : https://prove2.me/theorems/4836ca2d-0d54-4898-b1fd-23e9a090768d
-- title:
--   Residue: prod position
-- statement:
--   The Residue construction uses the prod position property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L21-L28

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

theorem PI.Residue.prod_position [Fintype ι] (N : α → ℕ) (idx : α → ι) (s : Multiset α) :
    ∏ i, intersection_update_fsHerm_neg_one N idx s i = (s.map N).prod := by sorry
