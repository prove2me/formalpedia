-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyX__ac9c7cc18615
-- name    : P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyX__ac9c7cc18615
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:10.932106+00:00
-- url     : https://prove2.me/theorems/332645d6-88d7-4f44-9003-08b879878da0
-- title:
--   P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts poly X  ac9c7cc18615: P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts poly X  ac9c7cc18615
-- statement:
--   The P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts poly X  ac9c7cc18615 construction uses the P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts poly X  ac9c7cc18615 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L354-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L354-L360

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

theorem P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyX__ac9c7cc18615 {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * X ≤ sg P K * P.b := by sorry

alias «Formalism».«LFunctionChainParameters».«PrimeWindowSizeBounds».«Facts».«polyX'» := P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyX__ac9c7cc18615
