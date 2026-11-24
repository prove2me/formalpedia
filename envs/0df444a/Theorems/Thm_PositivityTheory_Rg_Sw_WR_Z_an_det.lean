-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_det
-- name    : PositivityTheory.Rg.Sw.WR.Z.an_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:55.260571+00:00
-- url     : https://prove2.me/theorems/b6d09dd0-1ea9-4fb0-bee9-33460a29f437
-- title:
--   Z: an det
-- statement:
--   The Z construction uses the an det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L124-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L124-L136

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

theorem PositivityTheory.Rg.Sw.WR.Z.an_det {M : MC n → Matrix (Fin n) (Fin n) ℂ} {B₀ : MC n} (h : EntAn M B₀) :
    AnalyticAt ℂ (fun B => (M B).det) B₀ := by sorry
