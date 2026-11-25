-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_norm_cexp_neg_It
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.norm_cexp_neg_It
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:10.822545+00:00
-- url     : https://prove2.me/theorems/c336aa49-23fe-51de-95e3-a7e1238b9a34
-- title:
--   Moll: norm cexp neg It
-- statement:
--   The Moll construction uses the norm cexp neg It property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollId.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollId.lean#L18-L20

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.D.Moll.norm_cexp_neg_It (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by sorry
