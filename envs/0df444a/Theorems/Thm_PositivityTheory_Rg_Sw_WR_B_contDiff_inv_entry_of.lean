-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_inv_entry_of
-- name    : PositivityTheory.Rg.Sw.WR.B.contDiff_inv_entry_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:03.785036+00:00
-- url     : https://prove2.me/theorems/0410ca42-1ed7-4061-8f8a-4bf7cf233ce6
-- title:
--   B: cont Diff inv entry of
-- statement:
--   The B construction uses the cont Diff inv entry of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L141-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L141-L151

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

theorem PositivityTheory.Rg.Sw.WR.B.contDiff_inv_entry_of {M : E n → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => M y a b)) (hd : ∀ y, (M y).det ≠ 0) (a b : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (M y)⁻¹ a b) := by sorry
