-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qh34_aux2__09dfafc3a222
-- name    : P2M_UpperTheory_Reformulated_B_Qh34_aux2__09dfafc3a222
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:57.895924+00:00
-- url     : https://prove2.me/theorems/d9124545-2022-4f96-b66d-a38ec24d00e4
-- title:
--   P2 M Upper Theory Reformulated B Qh34 aux2  09dfafc3a222: P2 M Upper Theory Reformulated B Qh34 aux2  09dfafc3a222
-- statement:
--   The P2 M Upper Theory Reformulated B Qh34 aux2  09dfafc3a222 construction uses the P2 M Upper Theory Reformulated B Qh34 aux2  09dfafc3a222 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteTraceAlgebraMap.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteTraceAlgebraMap.lean#L15-L27

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

theorem P2M_UpperTheory_Reformulated_B_Qh34_aux2__09dfafc3a222.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x y : NumberField.InfiniteAdeleRing K),
      ∑ w : NumberField.InfinitePlace K,
          (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) ((x + y) w)).re =
        ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re +
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (y w)).re := by sorry

alias «UpperTheory».«Reformulated».«B».«Qh34».«aux2».«» := P2M_UpperTheory_Reformulated_B_Qh34_aux2__09dfafc3a222
