-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qh34_aux1__94f92b22043b
-- name    : P2M_UpperTheory_Reformulated_B_Qh34_aux1__94f92b22043b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:36.887722+00:00
-- url     : https://prove2.me/theorems/cbf68cad-0727-59ff-a1f7-9584bd07e5ae
-- title:
--   P2 M Upper Theory Reformulated B Qh34 aux1  94f92b22043b: P2 M Upper Theory Reformulated B Qh34 aux1  94f92b22043b
-- statement:
--   The P2 M Upper Theory Reformulated B Qh34 aux1  94f92b22043b construction uses the P2 M Upper Theory Reformulated B Qh34 aux1  94f92b22043b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteTraceAlgebraMap.lean#L3-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteTraceAlgebraMap.lean#L3-L13

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteTraceAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qh34_aux1__94f92b22043b.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],
      ∑ x : NumberField.InfinitePlace K,
          (↑x.mult : ℝ) *
            ((NumberField.InfinitePlace.Completion.extensionEmbedding x : x.Completion → ℂ)
                ((0 : NumberField.InfiniteAdeleRing K) x)).re =
        (0 : ℝ) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qh34».«aux1».«» := P2M_UpperTheory_Reformulated_B_Qh34_aux1__94f92b22043b
