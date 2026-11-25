-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_sum
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:50.186527+00:00
-- url     : https://prove2.me/theorems/46bf2a41-e36a-5be3-94d8-f4d3735d3743
-- title:
--   B: dir C sum
-- statement:
--   The B construction uses the dir C sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L153-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L153-L160

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

theorem PositivityTheory.Rg.Sw.WR.B.dirC_sum {ι : Type} (s : Finset ι) {f : ι → E n → ℂ} {y : E n} (hf : ∀ i, DifferentiableAt ℝ (f i) y)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => ∑ i ∈ s, f i x) w y = ∑ i ∈ s, dirC (f i) w y := by sorry
