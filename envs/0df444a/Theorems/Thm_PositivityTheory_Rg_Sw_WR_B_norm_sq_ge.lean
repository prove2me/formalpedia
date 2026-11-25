-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_sq_ge
-- name    : PositivityTheory.Rg.Sw.WR.B.norm_sq_ge
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:25.490479+00:00
-- url     : https://prove2.me/theorems/1cc21431-9847-46fa-a041-4845fb68a925
-- title:
--   B: norm sq ge
-- statement:
--   The B construction uses the norm sq ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L102-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L102-L112

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

theorem PositivityTheory.Rg.Sw.WR.B.norm_sq_ge {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y) (x : Fin n → ℂ) :
    ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖(M *ᵥ x) i‖ ^ 2 := by sorry
