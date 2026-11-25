-- Prove2me | Theorems.Thm_P2M_Formalism_LT_LTL_mem_span_of_norm_le__498e07ccaf2e
-- name    : P2M_Formalism_LT_LTL_mem_span_of_norm_le__498e07ccaf2e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:37.894507+00:00
-- url     : https://prove2.me/theorems/875b5e72-3a93-46af-a93f-884350559e8f
-- title:
--   P2 M Formalism LT LTL mem span of norm le  498e07ccaf2e: P2 M Formalism LT LTL mem span of norm le  498e07ccaf2e
-- statement:
--   The P2 M Formalism LT LTL mem span of norm le  498e07ccaf2e construction uses the P2 M Formalism LT LTL mem span of norm le  498e07ccaf2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L292-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L292-L302

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

theorem P2M_Formalism_LT_LTL_mem_span_of_norm_le__498e07ccaf2e {π : K} (hπ : ‖π‖ ≤ 1) (hπ0 : π ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖π‖) : x ∈ Ideal.span {piO π hπ} := by sorry

alias «Formalism».«LT».«LTL».«mem_span_of_norm_le'» := P2M_Formalism_LT_LTL_mem_span_of_norm_le__498e07ccaf2e
