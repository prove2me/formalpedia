-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504
-- name    : P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:56.125022+00:00
-- url     : https://prove2.me/theorems/3e6ae84e-3086-4cb3-9440-fe2ee98496f0
-- title:
--   P2 M Upper Theory Reformulated B Qf22 bi Hom sum  dada144c4504: P2 M Upper Theory Reformulated B Qf22 bi Hom sum  dada144c4504
-- statement:
--   The P2 M Upper Theory Reformulated B Qf22 bi Hom sum  dada144c4504 construction uses the P2 M Upper Theory Reformulated B Qf22 bi Hom sum  dada144c4504 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BiHomSum.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BiHomSum.lean#L10-L17

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504.{u_1} :
    ∀ {K ι κ : Type} [inst : Field K] [Fintype κ] {α : Type u_1} {d : ℕ} (s : Finset α)
      (F : α → MvPolynomial κ (MvPolynomial ι K)),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf22.biHom d (F a)) → UpperTheory.Reformulated.B.Qf22.biHom d (∑ a ∈ s, F a) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qf22».«biHom_sum».«» := P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504
