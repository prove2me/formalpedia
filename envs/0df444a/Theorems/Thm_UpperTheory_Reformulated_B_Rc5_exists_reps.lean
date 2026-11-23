-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Rc5_exists_reps
-- name    : UpperTheory.Reformulated.B.Rc5.exists_reps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:57.987803+00:00
-- url     : https://prove2.me/theorems/323e8d84-cb1f-49e6-b8de-765f1e69c595
-- title:
--   Rc5: exists reps
-- statement:
--   The Rc5 construction uses the exists reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsFurtherSide.lean#L3-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsFurtherSide.lean#L3-L34

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsFurtherSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Rc5.exists_reps :
    ∀ {α : Type} (r : α → α → Prop),
    (∀ (a b : α), r a b → r b a) →
      (∀ (a b c : α), r a b → r b c → r a c) →
        ∀ (t : Finset α), ∃ C ⊆ t, (∀ a ∈ C, ∀ b ∈ C, r a b → a = b) ∧ ∀ x ∈ t, x ∈ C ∨ ∃ c ∈ C, r x c := by sorry
