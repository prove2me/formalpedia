-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyv__5d511584b185
-- name    : P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyv__5d511584b185
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:49.859954+00:00
-- url     : https://prove2.me/theorems/36dec0ff-8f4b-4764-bfab-8a3ba02f1a3e
-- title:
--   P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts polyv  5d511584b185: P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts polyv  5d511584b185
-- statement:
--   The P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts polyv  5d511584b185 construction uses the P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts polyv  5d511584b185 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L362-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L362-L375

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
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
variable {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8)
include F

theorem P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyv__5d511584b185 {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * v ≤ sg P K * P.b := by sorry

alias «Formalism».«LFunctionChainParameters».«PrimeWindowSizeBounds».«Facts».«polyv'» := P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyv__5d511584b185
