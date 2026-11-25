-- Prove2me | Theorems.Thm_P2M_Formalism_ZeroFreeDirichlet_norm_le_norm_add_of_mem_closedBall__531c6a09be92
-- name    : P2M_Formalism_ZeroFreeDirichlet_norm_le_norm_add_of_mem_closedBall__531c6a09be92
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:13.45682+00:00
-- url     : https://prove2.me/theorems/8ae91a9f-2111-42b9-aab0-99e99a4243e3
-- title:
--   P2 M Formalism Zero Free Dirichlet norm le norm add of mem closed Ball  531c6a09be92: P2 M Formalism Zero Free Dirichlet norm le norm add of mem closed Ball  531c6a09be92
-- statement:
--   The P2 M Formalism Zero Free Dirichlet norm le norm add of mem closed Ball  531c6a09be92 construction uses the P2 M Formalism Zero Free Dirichlet norm le norm add of mem closed Ball  531c6a09be92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LogTwoLeLogAnalyticConductor.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LogTwoLeLogAnalyticConductor.lean#L39-L42

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem P2M_Formalism_ZeroFreeDirichlet_norm_le_norm_add_of_mem_closedBall__531c6a09be92 {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : ‖w‖ ≤ ‖z₀‖ + r := by sorry

alias «Formalism».«ZeroFreeDirichlet».«norm_le_norm_add_of_mem_closedBall'» := P2M_Formalism_ZeroFreeDirichlet_norm_le_norm_add_of_mem_closedBall__531c6a09be92
