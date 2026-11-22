-- Prove2me | Theorems.Thm_P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyXS__85083eb7ab8a
-- name    : P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyXS__85083eb7ab8a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:19.642458+00:00
-- url     : https://prove2.me/theorems/4c18ad36-779b-4f71-b95a-cf6779d5b764
-- title:
--   P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts poly XS  85083eb7ab8a: P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts poly XS  85083eb7ab8a
-- statement:
--   The P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts poly XS  85083eb7ab8a construction uses the P2 M Formalism LFunction Chain Parameters Prime Window Size Bounds Facts poly XS  85083eb7ab8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L343-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L343-L352

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

theorem P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyXS__85083eb7ab8a {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * (X * S) ≤ sg P K * P.b := by sorry

alias «Formalism».«LFunctionChainParameters».«PrimeWindowSizeBounds».«Facts».«polyXS'» := P2M_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_polyXS__85083eb7ab8a
