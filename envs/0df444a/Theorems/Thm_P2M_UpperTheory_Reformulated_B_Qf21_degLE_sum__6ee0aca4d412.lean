-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412
-- name    : P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:50.669568+00:00
-- url     : https://prove2.me/theorems/aed6ab98-f77b-4cba-8826-dd42857b6996
-- title:
--   P2 M Upper Theory Reformulated B Qf21 deg LE sum  6ee0aca4d412: P2 M Upper Theory Reformulated B Qf21 deg LE sum  6ee0aca4d412
-- statement:
--   The P2 M Upper Theory Reformulated B Qf21 deg LE sum  6ee0aca4d412 construction uses the P2 M Upper Theory Reformulated B Qf21 deg LE sum  6ee0aca4d412 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DegLESum.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DegLESum.lean#L8-L14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412.{u_1} :
    ∀ {κ R : Type} [inst : CommRing R] {α : Type u_1} {W : Finset κ} {n : ℕ} (s : Finset α) (F : α → MvPolynomial κ R),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf21.degLE W n (F a)) → UpperTheory.Reformulated.B.Qf21.degLE W n (∑ a ∈ s, F a) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qf21».«degLE_sum».«» := P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412
