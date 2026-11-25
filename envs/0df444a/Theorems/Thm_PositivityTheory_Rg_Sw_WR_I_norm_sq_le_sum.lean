-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_I_norm_sq_le_sum
-- name    : PositivityTheory.Rg.Sw.WR.I.norm_sq_le_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:44.354559+00:00
-- url     : https://prove2.me/theorems/b4ebf112-0764-4cbc-9800-50358b5f361d
-- title:
--   I: norm sq le sum
-- statement:
--   The I construction uses the norm sq le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/Integr.lean#L108-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/Integr.lean#L108-L120

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Integr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.I
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.I.norm_sq_le_sum (y : E n) : ‖y‖ ^ 2 ≤ ∑ a, ∑ b, y a b ^ 2 := by sorry
