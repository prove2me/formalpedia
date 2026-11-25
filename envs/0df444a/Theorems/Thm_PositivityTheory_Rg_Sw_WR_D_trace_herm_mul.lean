-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_trace_herm_mul
-- name    : PositivityTheory.Rg.Sw.WR.D.trace_herm_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:07.224855+00:00
-- url     : https://prove2.me/theorems/8b4cf7ad-2424-4253-a7df-d9fe6e403b2e
-- title:
--   D: trace herm mul
-- statement:
--   The D construction uses the trace herm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousEvX.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousEvX.lean#L38-L54

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.D.trace_herm_mul (y y' : E n) : (herm y * herm y').trace = ((ip y y' : ℝ) : ℂ) := by sorry
