-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_det_one_add_sq
-- name    : PositivityTheory.Rg.Sw.WR.Z.det_one_add_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:15.48181+00:00
-- url     : https://prove2.me/theorems/499ed9ac-6fd1-4140-be2c-278e5b42f131
-- title:
--   Z: det one add sq
-- statement:
--   The Z construction uses the det one add sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L71-L73

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

theorem PositivityTheory.Rg.Sw.WR.Z.det_one_add_sq (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (1 + herm y * herm y).det = ((Complex.normSq (1 - (Complex.I * s) • herm y).det : ℝ) : ℂ) := by sorry
