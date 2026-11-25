-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_delta_step
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.TW.delta_step
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:08:53.112479+00:00
-- url     : https://prove2.me/theorems/ffeecaf5-e6af-5266-b34f-279110704fc4
-- title:
--   TW: delta step
-- statement:
--   The TW construction uses the delta step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean#L213-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean#L213-L223

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.K.GB.TW.delta_step (z : ℂ) (c : ℕ → E n → ℂ) (M : ℕ) (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j))
    (hM : ∀ j, M ≤ j → c j = 0) :
    Delta (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + n), z ^ j * TDelta c j y := by sorry
