-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_RemovableSingularityAlt_analyticAt_dslope
-- name    : PositivityTheory.RgJS.RemovableSingularityAlt.analyticAt_dslope
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:06.224489+00:00
-- url     : https://prove2.me/theorems/15db7124-7f73-4807-9484-9ae36ab0cde8
-- title:
--   Removable Singularity Alt: analytic At dslope
-- statement:
--   The Removable Singularity Alt construction uses the analytic At dslope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/RemovableSingularities/RemovableSingularityHolds.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/RemovableSingularities/RemovableSingularityHolds.lean#L15-L26

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_RemovableSingularities_RemovableSingularityHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.RemovableSingularityAlt

theorem PositivityTheory.RgJS.RemovableSingularityAlt.analyticAt_dslope {f : ℂ → ℂ} {z : ℂ} (h1 : AnalyticAt ℂ f 1) (hz : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (dslope f 1) z := by sorry
