-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64
-- name    : P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:23.651652+00:00
-- url     : https://prove2.me/theorems/5f8a90e0-83b9-5ab9-998d-7df8456f6399
-- title:
--   P2 M Upper Theory Reformulated B Qe24 span S induction  ec3676585f64: P2 M Upper Theory Reformulated B Qe24 span S induction  ec3676585f64
-- statement:
--   The P2 M Upper Theory Reformulated B Qe24 span S induction  ec3676585f64 construction uses the P2 M Upper Theory Reformulated B Qe24 span S induction  ec3676585f64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SpanSInduction.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SpanSInduction.lean#L13-L27

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {n : ℕ} {x : Fin n → V} {p : V → Prop},
      p (0 : V) →
        (∀ (a b : V), p a → p b → p (a + b)) →
          (∀ c ∈ S, ∀ (a : V), p a → p (c • a)) → (∀ (i : Fin n), p (x i)) → ∀ v ∈ UpperTheory.Reformulated.B.Qe24.spanS S x, p v := by sorry

alias «UpperTheory».«Reformulated».«B».«Qe24».«spanS_induction».«» := P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64
