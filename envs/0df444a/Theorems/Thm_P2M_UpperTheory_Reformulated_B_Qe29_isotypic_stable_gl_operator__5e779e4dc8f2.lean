-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qe29_isotypic_stable_gl_operator__5e779e4dc8f2
-- name    : P2M_UpperTheory_Reformulated_B_Qe29_isotypic_stable_gl_operator__5e779e4dc8f2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:39.188447+00:00
-- url     : https://prove2.me/theorems/72a1be28-5153-4884-8919-9a570ab1149a
-- title:
--   P2 M Upper Theory Reformulated B Qe29 isotypic stable gl operator  5e779e4dc8f2: P2 M Upper Theory Reformulated B Qe29 isotypic stable gl operator  5e779e4dc8f2
-- statement:
--   The P2 M Upper Theory Reformulated B Qe29 isotypic stable gl operator  5e779e4dc8f2 construction uses the P2 M Upper Theory Reformulated B Qe29 isotypic stable gl operator  5e779e4dc8f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsotypicStableGlOperator.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsotypicStableGlOperator.lean#L58-L68

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsotypicStableGlOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qe29_isotypic_stable_gl_operator__5e779e4dc8f2.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n),
      ∀ x ∈ UpperTheory.Reformulated.B.Qe29.isoSub E mu, (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qe29.isoSub E mu := by sorry

alias «UpperTheory».«Reformulated».«B».«Qe29».«isotypic_stable_gl_operator» := P2M_UpperTheory_Reformulated_B_Qe29_isotypic_stable_gl_operator__5e779e4dc8f2
