-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_SmoothOnAdditive_main__f00fdea2d781
-- name    : P2M_UpperTheory_Reformulated_B_SmoothOnAdditive_main__f00fdea2d781
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:37.813388+00:00
-- url     : https://prove2.me/theorems/31337869-c243-50c1-82c7-161dfd95c8e7
-- title:
--   P2 M Upper Theory Reformulated B Smooth On Additive main  f00fdea2d781: P2 M Upper Theory Reformulated B Smooth On Additive main  f00fdea2d781
-- statement:
--   The P2 M Upper Theory Reformulated B Smooth On Additive main  f00fdea2d781 construction uses the P2 M Upper Theory Reformulated B Smooth On Additive main  f00fdea2d781 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SmoothOnAdditive.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SmoothOnAdditive.lean#L35-L50

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers

theorem P2M_UpperTheory_Reformulated_B_SmoothOnAdditive_main__f00fdea2d781.{u_1, u_2, u_3} :
    ∀ {E : Type u_1} {V : Type u_2} {ι : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
      [inst_2 : NormedAddCommGroup V] [inst_3 : NormedSpace ℝ V] {A : Set E} {f : ι → E → V} (s : Finset ι),
      (∀ i ∈ s, UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (f i)) → UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A fun (a : E) ↦ ∑ i ∈ s, f i a := by sorry

alias «UpperTheory».«Reformulated».«B».«SmoothOnAdditive».«main».«» := P2M_UpperTheory_Reformulated_B_SmoothOnAdditive_main__f00fdea2d781
