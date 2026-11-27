-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Yhb6_main__b0b20f5070cf
-- name    : P2M_UpperTheory_Reformulated_B_Yhb6_main__b0b20f5070cf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:13.734001+00:00
-- url     : https://prove2.me/theorems/c477d14e-d94a-5049-9432-8c0ac951e11b
-- title:
--   P2 M Upper Theory Reformulated B Yhb6 main  b0b20f5070cf: P2 M Upper Theory Reformulated B Yhb6 main  b0b20f5070cf
-- statement:
--   The P2 M Upper Theory Reformulated B Yhb6 main  b0b20f5070cf construction uses the P2 M Upper Theory Reformulated B Yhb6 main  b0b20f5070cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CardFiber.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CardFiber.lean#L13-L26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Yhb6_main__b0b20f5070cf.{u_1} :
    ∀ {α : Type u_1} {l : ℕ} {x y : Fin l → α},
      Multiset.map y Finset.univ.val = Multiset.map x Finset.univ.val →
        ∃ (e : Equiv.Perm (Fin l)), ∀ (a : Fin l), y a = x ((e : Fin l → Fin l) a) := by sorry

alias «UpperTheory».«Reformulated».«B».«Yhb6».«main».«» := P2M_UpperTheory_Reformulated_B_Yhb6_main__b0b20f5070cf
