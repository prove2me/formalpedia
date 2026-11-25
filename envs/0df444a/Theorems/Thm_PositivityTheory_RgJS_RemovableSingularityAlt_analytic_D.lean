-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_RemovableSingularityAlt_analytic_D
-- name    : PositivityTheory.RgJS.RemovableSingularityAlt.analytic_D
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:04.262547+00:00
-- url     : https://prove2.me/theorems/a36384a1-4090-41b5-986d-1c8f8369dbe0
-- title:
--   Removable Singularity Alt: analytic D
-- statement:
--   The Removable Singularity Alt construction uses the analytic D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/RemovableSingularities/RemovableSingularityHolds.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/RemovableSingularities/RemovableSingularityHolds.lean#L28-L34

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

theorem PositivityTheory.RgJS.RemovableSingularityAlt.analytic_D {G : ℂ → ℂ} (hG : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ) :
    ∀ j, ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ (D G j) σ
  := by sorry
