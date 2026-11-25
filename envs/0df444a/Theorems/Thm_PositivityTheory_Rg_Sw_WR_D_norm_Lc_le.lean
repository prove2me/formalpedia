-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_Lc_le
-- name    : PositivityTheory.Rg.Sw.WR.D.norm_Lc_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:29.669371+00:00
-- url     : https://prove2.me/theorems/6cc669ff-56d5-4518-a895-b0f7ff170a4e
-- title:
--   D: norm Lc le
-- statement:
--   The D construction uses the norm Lc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L52-L62

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

theorem PositivityTheory.Rg.Sw.WR.D.norm_Lc_le (q : E n) : ‖Lc q‖ ≤ ∑ a, ∑ b, |q a b| := by sorry
