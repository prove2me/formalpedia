-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux2__390a7bbeff16
-- name    : P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux2__390a7bbeff16
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:16.418273+00:00
-- url     : https://prove2.me/theorems/d79d0cb0-9d23-499a-a125-71fd3b335e75
-- title:
--   P2 M Upper Theory Reformulated B Selection Lemmas aux2  390a7bbeff16: P2 M Upper Theory Reformulated B Selection Lemmas aux2  390a7bbeff16
-- statement:
--   The P2 M Upper Theory Reformulated B Selection Lemmas aux2  390a7bbeff16 construction uses the P2 M Upper Theory Reformulated B Selection Lemmas aux2  390a7bbeff16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean#L15-L25

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux2__390a7bbeff16.{u_1} :
    ∀ {K : Type u_1} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))) := by sorry

alias «UpperTheory».«Reformulated».«B».«SelectionLemmas».«aux2» := P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux2__390a7bbeff16
