-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_mem_pdisc_self
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.mem_pdisc_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:14.631156+00:00
-- url     : https://prove2.me/theorems/6e8108b4-f122-4cf6-bf76-a0d3833cfd06
-- title:
--   GB: mem pdisc self
-- statement:
--   The GB construction uses the mem pdisc self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBCauchy.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBCauchy.lean#L30-L33

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.mem_pdisc_self (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) : b ∈ pdisc b r := by sorry
