-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qf26_tmA_sm_sum__1a2d79d19c55
-- name    : P2M_UpperTheory_Reformulated_B_Qf26_tmA_sm_sum__1a2d79d19c55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:58.761923+00:00
-- url     : https://prove2.me/theorems/6acfc294-1bb1-4461-a501-bbddcc6c4495
-- title:
--   P2 M Upper Theory Reformulated B Qf26 tm A sm sum  1a2d79d19c55: P2 M Upper Theory Reformulated B Qf26 tm A sm sum  1a2d79d19c55
-- statement:
--   The P2 M Upper Theory Reformulated B Qf26 tm A sm sum  1a2d79d19c55 construction uses the P2 M Upper Theory Reformulated B Qf26 tm A sm sum  1a2d79d19c55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TmASmSum.lean#L80-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TmASmSum.lean#L80-L95

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TmASmSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qf26_tmA_sm_sum__1a2d79d19c55.{u_1} :
    ∀ {n : Nat} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) Complex → Complex),
      (∀ (i : ι),
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @UpperTheory.Reformulated.B.Qf26.SmoothOnG n ε (F i)) →
        @UpperTheory.Reformulated.B.Qf26.SmoothOnG n ε fun (x : Matrix (Fin n) (Fin n) Complex) ↦ ∑ i ∈ s, F i x := by sorry

alias «UpperTheory».«Reformulated».«B».«Qf26».«tmA_sm_sum».«» := P2M_UpperTheory_Reformulated_B_Qf26_tmA_sm_sum__1a2d79d19c55
