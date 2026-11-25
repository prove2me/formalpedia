-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_EvaluationMap_main
-- name    : UpperTheory.Reformulated.B.EvaluationMap.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:39:10.750799+00:00
-- url     : https://prove2.me/theorems/dd97c147-1395-5701-b3d9-e5c0c99fd3d8
-- title:
--   Evaluation Map: main
-- statement:
--   The Evaluation Map construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvaluationMap.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvaluationMap.lean#L28-L37

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvaluationMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open UpperTheory.Reformulated.B.EvaluationMap.Helpers

theorem UpperTheory.Reformulated.B.EvaluationMap.main :
    ∀ {K W : Type} [inst : Group K] [inst_1 : AddCommGroup W] [inst_2 : _root_.Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ K W), FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ) := by sorry
