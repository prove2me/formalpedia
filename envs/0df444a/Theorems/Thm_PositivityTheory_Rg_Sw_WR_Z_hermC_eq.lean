-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_hermC_eq
-- name    : PositivityTheory.Rg.Sw.WR.Z.hermC_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:47.766938+00:00
-- url     : https://prove2.me/theorems/514c8487-28d5-4462-bc8b-c153e6e84e11
-- title:
--   Z: herm C eq
-- statement:
--   The Z construction uses the herm C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L240-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L240-L247

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

theorem PositivityTheory.Rg.Sw.WR.Z.hermC_eq (w : Fin n → Fin n → ℂ) :
    hermL (fun a b => (w a b).re) + Complex.I • hermL (fun a b => (w a b).im) =
      fun i j => (w i j + w j i) / 2 + Complex.I * (w i j - w j i) / 2 := by sorry
