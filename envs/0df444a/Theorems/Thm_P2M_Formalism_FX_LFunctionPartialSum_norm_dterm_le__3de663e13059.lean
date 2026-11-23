-- Prove2me | Theorems.Thm_P2M_Formalism_FX_LFunctionPartialSum_norm_dterm_le__3de663e13059
-- name    : P2M_Formalism_FX_LFunctionPartialSum_norm_dterm_le__3de663e13059
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:29.996313+00:00
-- url     : https://prove2.me/theorems/46a69347-a80b-4bd0-963f-d085d699d9f7
-- title:
--   P2 M Formalism FX LFunction Partial Sum norm dterm le  3de663e13059: P2 M Formalism FX LFunction Partial Sum norm dterm le  3de663e13059
-- statement:
--   The P2 M Formalism FX LFunction Partial Sum norm dterm le  3de663e13059 construction uses the P2 M Formalism FX LFunction Partial Sum norm dterm le  3de663e13059 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L110-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L110-L119

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
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem P2M_Formalism_FX_LFunctionPartialSum_norm_dterm_le__3de663e13059 {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm χ s n‖ ≤ B * (‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re))) := by sorry

alias «Formalism».«FX».«LFunctionPartialSum».«norm_dterm_le'» := P2M_Formalism_FX_LFunctionPartialSum_norm_dterm_le__3de663e13059
