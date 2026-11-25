-- Prove2me | Theorems.Thm_P2M_Formalism_LT_LTL_integralMv_X__f8764449aa3b
-- name    : P2M_Formalism_LT_LTL_integralMv_X__f8764449aa3b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:34.288702+00:00
-- url     : https://prove2.me/theorems/d867d7bb-0c16-4429-acf2-0cdc75714a85
-- title:
--   P2 M Formalism LT LTL integral Mv X  f8764449aa3b: P2 M Formalism LT LTL integral Mv X  f8764449aa3b
-- statement:
--   The P2 M Formalism LT LTL integral Mv X  f8764449aa3b construction uses the P2 M Formalism LT LTL integral Mv X  f8764449aa3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L357-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L357-L361

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

theorem P2M_Formalism_LT_LTL_integralMv_X__f8764449aa3b (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by sorry

alias «Formalism».«LT».«LTL».«integralMv_X'» := P2M_Formalism_LT_LTL_integralMv_X__f8764449aa3b
