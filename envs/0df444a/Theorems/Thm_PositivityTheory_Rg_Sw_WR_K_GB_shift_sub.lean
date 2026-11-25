-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_shift_sub
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.shift_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:51:59.760089+00:00
-- url     : https://prove2.me/theorems/8fea4de3-32fe-5614-886f-a4b80814815f
-- title:
--   GB: shift sub
-- statement:
--   The GB construction uses the shift sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBCauchy.lean#L52-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBCauchy.lean#L52-L71

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBCauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.K.GB.shift_sub (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    {K l : ℝ} (hK : 0 < K) (hl : 0 ≤ l) (hlK : l + 1 = K) (hw : ‖w‖ = r i j / K) :
    pdisc (b + w • Matrix.single i j (1 : ℂ)) (fun a c => r a c * (l / K)) ⊆ pdisc b r := by sorry
