-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_dirC_comp
-- name    : PositivityTheory.Rg.Sw.WR.Z.dirC_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:09:31.515802+00:00
-- url     : https://prove2.me/theorems/ca364dd0-377a-52ca-9efd-98983538f068
-- title:
--   Z: dir C comp
-- statement:
--   The Z construction uses the dir C comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L230-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L230-L238

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

theorem PositivityTheory.Rg.Sw.WR.Z.dirC_comp (G : MC n → ℂ) (y : E n) (hG : DifferentiableAt ℂ G (herm y)) (w : Fin n → Fin n → ℂ) :
    dirC (fun y => G (herm y)) w y =
      fderiv ℂ G (herm y) (hermL (fun a b => (w a b).re) + Complex.I • hermL (fun a b => (w a b).im)) := by sorry
