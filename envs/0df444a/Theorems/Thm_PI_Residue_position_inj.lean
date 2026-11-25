-- Prove2me | Theorems.Thm_PI_Residue_position_inj
-- name    : PI.Residue.position_inj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:21.699283+00:00
-- url     : https://prove2.me/theorems/b3d2107e-3e38-4b68-a1b5-883e09b8bab6
-- title:
--   Residue: position inj
-- statement:
--   The Residue construction uses the position inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L69-L83

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

theorem PI.Residue.position_inj (N : α → ℕ) (idx : α → ι) (S : Set α) (h1 : ∀ a ∈ S, 1 < N a)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, idx a = idx b → ¬ Nat.Coprime (N a) (N b) → a = b)
    {s t : Multiset α} (hs : ∀ a ∈ s, a ∈ S) (ht : ∀ a ∈ t, a ∈ S)
    (h : intersection_update_fsHerm_neg_one N idx s = intersection_update_fsHerm_neg_one N idx t) : s = t := by sorry
