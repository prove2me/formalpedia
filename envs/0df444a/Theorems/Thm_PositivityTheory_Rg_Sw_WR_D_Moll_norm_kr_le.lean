-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_norm_kr_le
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.norm_kr_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:07:04.762733+00:00
-- url     : https://prove2.me/theorems/0942629e-3da0-5a11-b999-d2ce1e45f75d
-- title:
--   Moll: norm kr le
-- statement:
--   The Moll construction uses the norm kr le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollId.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/MollId.lean#L45-L49

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

theorem PositivityTheory.Rg.Sw.WR.D.Moll.norm_kr_le (ε t : ℝ) (hε : 0 < ε) (u : E n) : ‖kr ε t u‖ ≤ ∫ y, ‖gam (n := n) ε y‖ := by sorry
