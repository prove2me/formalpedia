-- Prove2me | Theorems.Thm_PI_Residue_factorization_position
-- name    : PI.Residue.factorization_position
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:17.893116+00:00
-- url     : https://prove2.me/theorems/16fe8484-ee97-57f0-9b37-6aa504b5c15b
-- title:
--   Residue: factorization position
-- statement:
--   The Residue construction uses the factorization position property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L43-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L43-L67

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

theorem PI.Residue.factorization_position (N : α → ℕ) (idx : α → ι) (S : Set α) (h1 : ∀ a ∈ S, 1 < N a)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, idx a = idx b → ¬ Nat.Coprime (N a) (N b) → a = b)
    {s : Multiset α} (hs : ∀ a ∈ s, a ∈ S) {a : α} (ha : a ∈ S) :
    (intersection_update_fsHerm_neg_one N idx s (idx a)).factorization (N a).minFac
      = s.count a * (N a).factorization (N a).minFac := by sorry
