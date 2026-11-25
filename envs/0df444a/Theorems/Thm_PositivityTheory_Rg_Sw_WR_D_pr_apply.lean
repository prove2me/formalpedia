-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_pr_apply
-- name    : PositivityTheory.Rg.Sw.WR.D.pr_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:20.455872+00:00
-- url     : https://prove2.me/theorems/12a0292f-3ae7-5394-b5b9-911028171018
-- title:
--   D: pr apply
-- statement:
--   The D construction uses the pr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L42-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L42-L42

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.D.pr_apply (a b : Fin n) (w : E n) : pr a b w = w a b := by sorry
