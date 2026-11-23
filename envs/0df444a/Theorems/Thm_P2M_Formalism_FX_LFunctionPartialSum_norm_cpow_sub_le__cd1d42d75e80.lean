-- Prove2me | Theorems.Thm_P2M_Formalism_FX_LFunctionPartialSum_norm_cpow_sub_le__cd1d42d75e80
-- name    : P2M_Formalism_FX_LFunctionPartialSum_norm_cpow_sub_le__cd1d42d75e80
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:29.540103+00:00
-- url     : https://prove2.me/theorems/2f522401-6b84-4768-9464-51ed9d20c3c5
-- title:
--   P2 M Formalism FX LFunction Partial Sum norm cpow sub le  cd1d42d75e80: P2 M Formalism FX LFunction Partial Sum norm cpow sub le  cd1d42d75e80
-- statement:
--   The P2 M Formalism FX LFunction Partial Sum norm cpow sub le  cd1d42d75e80 construction uses the P2 M Formalism FX LFunction Partial Sum norm cpow sub le  cd1d42d75e80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L69-L73

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum

theorem P2M_Formalism_FX_LFunctionPartialSum_norm_cpow_sub_le__cd1d42d75e80 {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by sorry

alias «Formalism».«FX».«LFunctionPartialSum».«norm_cpow_sub_le'» := P2M_Formalism_FX_LFunctionPartialSum_norm_cpow_sub_le__cd1d42d75e80
