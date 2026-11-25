-- Prove2me | Theorems.Thm_P2M_Formalism_LT_LTL_norm_le_of_mem_span__3b10f192d90f
-- name    : P2M_Formalism_LT_LTL_norm_le_of_mem_span__3b10f192d90f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:34.31691+00:00
-- url     : https://prove2.me/theorems/9a54e1b8-b663-4253-9afc-5e64948a2a11
-- title:
--   P2 M Formalism LT LTL norm le of mem span  3b10f192d90f: P2 M Formalism LT LTL norm le of mem span  3b10f192d90f
-- statement:
--   The P2 M Formalism LT LTL norm le of mem span  3b10f192d90f construction uses the P2 M Formalism LT LTL norm le of mem span  3b10f192d90f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L283-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L283-L290

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem P2M_Formalism_LT_LTL_norm_le_of_mem_span__3b10f192d90f {π : K} (hπ : ‖π‖ ≤ 1) (x : unitBall K)
    (hx : x ∈ Ideal.span {piO π hπ}) : ‖(x : K)‖ ≤ ‖π‖ := by sorry

alias «Formalism».«LT».«LTL».«norm_le_of_mem_span'» := P2M_Formalism_LT_LTL_norm_le_of_mem_span__3b10f192d90f
