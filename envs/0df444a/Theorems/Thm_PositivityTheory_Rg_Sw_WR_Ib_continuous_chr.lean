-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_continuous_chr
-- name    : PositivityTheory.Rg.Sw.WR.Ib.continuous_chr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:56.739069+00:00
-- url     : https://prove2.me/theorems/984e322a-983c-4a73-9271-e00d1c797621
-- title:
--   Ib: continuous chr
-- statement:
--   The Ib construction uses the continuous chr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L48-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L48-L48

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.Ib.continuous_chr (t : ℝ) (β : E n) : Continuous (chr t β) := by sorry
