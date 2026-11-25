-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qh28_isotypic_stable_operator__eba46ace8303
-- name    : P2M_UpperTheory_Reformulated_B_Qh28_isotypic_stable_operator__eba46ace8303
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:30.457898+00:00
-- url     : https://prove2.me/theorems/f0fd9622-057e-4669-87c4-0912b5e41511
-- title:
--   P2 M Upper Theory Reformulated B Qh28 isotypic stable operator  eba46ace8303: P2 M Upper Theory Reformulated B Qh28 isotypic stable operator  eba46ace8303
-- statement:
--   The P2 M Upper Theory Reformulated B Qh28 isotypic stable operator  eba46ace8303 construction uses the P2 M Upper Theory Reformulated B Qh28 isotypic stable operator  eba46ace8303 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsotypicStableOperator.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsotypicStableOperator.lean#L58-L67

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsotypicStableOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qh28_isotypic_stable_operator__eba46ace8303.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V},
      x ∈ UpperTheory.Reformulated.B.Qh28.isoSub E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qh28.isoSub E mu := by sorry

alias «UpperTheory».«Reformulated».«B».«Qh28».«isotypic_stable_operator» := P2M_UpperTheory_Reformulated_B_Qh28_isotypic_stable_operator__eba46ace8303
