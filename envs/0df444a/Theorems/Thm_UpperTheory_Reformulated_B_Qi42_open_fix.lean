-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qi42_open_fix
-- name    : UpperTheory.Reformulated.B.Qi42.open_fix
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:59.010842+00:00
-- url     : https://prove2.me/theorems/eb03b265-43e2-4d30-9228-9c48480f42af
-- title:
--   Qi42: open fix
-- statement:
--   The Qi42 construction uses the open fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/OpenFix.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/OpenFix.lean#L11-L16

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_OpenFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qi42.open_fix :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] (H : Subgroup (UpperTheory.Reformulated.B.Qi42.GQ v)),
      IsOpen (↑H : Set (UpperTheory.Reformulated.B.Qi42.GQ v)) → (IntermediateField.fixedField H).fixingSubgroup = H := by sorry
