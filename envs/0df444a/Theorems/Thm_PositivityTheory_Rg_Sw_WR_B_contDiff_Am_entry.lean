-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_Am_entry
-- name    : PositivityTheory.Rg.Sw.WR.B.contDiff_Am_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:40.196548+00:00
-- url     : https://prove2.me/theorems/e5d3d9a9-75bb-4f10-9b29-60d0f2adb25e
-- title:
--   B: cont Diff Am entry
-- statement:
--   The B construction uses the cont Diff Am entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L206-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L206-L208

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.contDiff_Am_entry (s : ℂ) (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y => Am s y a b) := by sorry
