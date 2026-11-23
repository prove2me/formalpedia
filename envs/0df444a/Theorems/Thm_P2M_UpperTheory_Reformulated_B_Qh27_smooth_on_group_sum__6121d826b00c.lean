-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c
-- name    : P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:33.929063+00:00
-- url     : https://prove2.me/theorems/0beb572f-e091-4b33-913c-761e5684ae6c
-- title:
--   P2 M Upper Theory Reformulated B Qh27 smooth on group sum  6121d826b00c: P2 M Upper Theory Reformulated B Qh27 smooth on group sum  6121d826b00c
-- statement:
--   The P2 M Upper Theory Reformulated B Qh27 smooth on group sum  6121d826b00c construction uses the P2 M Upper Theory Reformulated B Qh27 smooth on group sum  6121d826b00c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SmoothOnGroupSum.lean#L80-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SmoothOnGroupSum.lean#L80-L94

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c.{u_1} :
    ∀ {n : Nat} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) Complex → Complex),
      (∀ (i : ι),
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @UpperTheory.Reformulated.B.Qh27.SmoothOnG n ε (f i)) →
        @UpperTheory.Reformulated.B.Qh27.SmoothOnG n ε fun (x : Matrix (Fin n) (Fin n) Complex) ↦ ∑ i ∈ s, f i x := by sorry

alias «UpperTheory».«Reformulated».«B».«Qh27».«smooth_on_group_sum».«» := P2M_UpperTheory_Reformulated_B_Qh27_smooth_on_group_sum__6121d826b00c
