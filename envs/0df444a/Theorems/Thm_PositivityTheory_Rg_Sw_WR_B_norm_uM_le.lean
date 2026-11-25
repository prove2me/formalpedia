-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_uM_le
-- name    : PositivityTheory.Rg.Sw.WR.B.norm_uM_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:00:47.589852+00:00
-- url     : https://prove2.me/theorems/09c78066-a743-4196-a5ee-ce7d17f5c3ab
-- title:
--   B: norm u M le
-- statement:
--   The B construction uses the norm u M le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L135-L137

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.norm_uM_le {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b : Fin n) : ‖uM s y a b‖ ≤ 1 := by sorry
