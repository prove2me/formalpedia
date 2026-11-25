-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_cay
-- name    : PositivityTheory.Rg.Sw.WR.Z.an_cay
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:06:43.651717+00:00
-- url     : https://prove2.me/theorems/f5e452c1-db1c-58d2-840a-b0b82141bed9
-- title:
--   Z: an cay
-- statement:
--   The Z construction uses the an cay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L318-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L318-L329

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.Z.an_cay (U : Set (MC n)) (hU : IsOpen U) (G : MC n → ℂ) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (cay G) U := by sorry
