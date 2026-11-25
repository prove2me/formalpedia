-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale1__403e671ab8fd
-- name    : P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale1__403e671ab8fd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:44.958278+00:00
-- url     : https://prove2.me/theorems/169520bb-f591-4680-8942-a27fa4dab678
-- title:
--   P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds scale1  403e671ab8fd: P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds scale1  403e671ab8fd
-- statement:
--   The P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds scale1  403e671ab8fd construction uses the P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds scale1  403e671ab8fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L164-L168

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr

theorem P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale1__403e671ab8fd {m T q c b : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) (hcb : 0 ≤ c * b) (h : q ≤ c * b) :
    m * q ≤ c * (T * m * b) := by sorry

alias «Formalism».«LFunctionChainParameters».«PrimeWindowSizeBounds».«scale1'» := P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_scale1__403e671ab8fd
